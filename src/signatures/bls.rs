//! BLS Signatures
//!
//! Implements Boneh–Lynn–Shacham (BLS) digital signatures using ronkathon's
//! existing curve and pairing primitives. This module demonstrates key generation,
//! signing, verification, and aggregation (for signatures on the same message).
use crypto_bigint::{Encoding, U256};
use rand::Rng;

use crate::{
  algebra::{
    field::{
      extension::GaloisField,
      prime::{PlutoBaseField, PlutoScalarField},
      Field,
    },
    group::FiniteCyclicGroup,
    Finite,
  },
  curve::{self, pairing::pairing, pluto_curve::PlutoExtendedCurve, AffinePoint},
  hashes::sha3::Sha3_256 as Sha256,
  hmac::hmac_sha256::hmac_sha256,
};

/// Errors that can occur during BLS signature operations.
#[derive(Debug)]
pub enum BlsError {
  /// The provided public key is invalid.
  InvalidPublicKey,
  /// The signature is invalid.
  InvalidSignature,
  /// Hash-to-curve failed to find a valid point on the curve.
  HashToCurveFailed,
  /// Signature verification failed.
  VerificationFailed,
  /// Other error with a descriptive message.
  Other(String),
}

/// BLS private key.
pub struct BlsPrivateKey {
  sk: PlutoScalarField,
}

/// BLS public key.
pub struct BlsPublicKey {
  pk: AffinePoint<PlutoExtendedCurve>,
}

/// BLS signature.
pub struct BlsSignature {
  sig: AffinePoint<PlutoExtendedCurve>,
}

/// Converts a nonnegative integer to an octet string of a specified length using crypto-bigint.
///
/// I2OSP (Integer-to-Octet-String Primitive) converts a nonnegative integer `x` (represented as a
/// 256-bit integer) into its big-endian representation, trimmed of any excess leading zeroes, and
/// left-padded with zeroes so that the result has exactly `length` bytes.
///
/// # Arguments
///
/// * `x` - A reference to a `U256` representing the nonnegative integer.
/// * `length` - The number of octets (bytes) the output string should have.
///
/// # Returns
///
/// * `Ok(Vec<u8>)` containing the octet string if the integer can be represented in the specified
///   length.
/// * `Err(String)` if the integer is too large to be encoded in the given number of octets.
///
/// # Example
///
/// ```
/// use crypto_bigint::U256;
///
/// use crate::dsa::utils::i2osp;
///
/// let x = U256::from(65535u64);
/// let os = i2osp(&x, 4).unwrap();
/// assert_eq!(os, vec![0, 0, 255, 255]);
/// ```
pub fn i2osp(x: &U256, length: usize) -> Result<Vec<u8>, String> {
  // U256 is internally represented as 32 bytes (big-endian).
  let full_bytes = x.to_be_bytes(); // This is a [u8; 32].

  // Convert to a minimal representation by skipping all leading zeros.
  let minimal: Vec<u8> = {
    let buf: Vec<u8> = full_bytes.iter().skip_while(|&&b| b == 0).cloned().collect();
    if buf.is_empty() {
      vec![0]
    } else {
      buf
    }
  };

  if minimal.len() > length {
    return Err(format!("Integer too large to encode in {} octets", length));
  }
  let mut result = vec![0u8; length - minimal.len()];
  result.extend_from_slice(&minimal);
  Ok(result)
}

/// Converts an octet string to a nonnegative integer as a U256 using crypto-bigint.
///
/// OS2IP (Octet-String-to-Integer Primitive) interprets an octet string as the big-endian
/// representation of a nonnegative integer. When the input slice is longer than 32 bytes, the
/// function verifies that the extra leading bytes are all zero (so that the value fits in 256
/// bits).
///
/// # Arguments
///
/// * `octets` - A slice of bytes representing the octet string.
///
/// # Returns
///
/// * `Ok(U256)` corresponding to the nonnegative integer value of `octets`.
/// * `Err(String)` if the octet string represents a number that does not fit in 256 bits.
///
/// # Example
///
/// ```
/// use crypto_bigint::U256;
///
/// use crate::dsa::utils::os2ip;
///
/// let bytes = vec![0, 0, 255, 255];
/// let x = os2ip(&bytes).unwrap();
/// assert_eq!(x, U256::from(65535u64));
/// ```
pub fn os2ip(octets: &[u8]) -> Result<U256, String> {
  let len = octets.len();
  if len > 32 {
    // For slices longer than 32 bytes, verify that the extra (leftmost) bytes are all zero.
    if octets[..len - 32].iter().any(|&b| b != 0) {
      return Err("Integer too large to represent in 256 bits".to_string());
    }
    let arr: [u8; 32] = octets[len - 32..].try_into().map_err(|_| "Invalid slice length")?;
    Ok(U256::from_be_bytes(arr))
  } else {
    // If fewer than 32 bytes, left-pad with zeros.
    let mut padded = [0u8; 32];
    padded[32 - len..].copy_from_slice(octets);
    Ok(U256::from_be_bytes(padded))
  }
}

// HKDF

/// HKDF-Extract according to RFC 5869.
/// If no salt is provided (i.e., salt is empty), a zero-filled salt of 32-bytes (SHA-256 output
/// length) is used.
pub fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> Vec<u8> {
  let salt = if salt.is_empty() {
    // For SHA-256, the hash length is 32 bytes.
    vec![0u8; 32]
  } else {
    salt.to_vec()
  };
  hmac_sha256(&salt, ikm).to_vec()
}

/// HKDF-Expand according to RFC 5869.
pub fn hkdf_expand(prk: &[u8], info: &[u8], l: usize) -> Vec<u8> {
  // Optionally: enforce l <= 255 * 32 if using SHA-256
  let n = (l + 31) / 32; // Ceiling division for hash length of 32 bytes
  let mut t = Vec::new(); // This will hold T(i-1), starting with empty T(0)
  let mut okm = Vec::new();
  for i in 1..=n {
    // Create message: T(i-1) || info || i
    let mut data = Vec::new();
    data.extend_from_slice(&t);
    data.extend_from_slice(info);
    data.push(i as u8);

    // Compute T(i)
    t = hmac_sha256(prk, &data).to_vec();

    // Append T(i) to the output
    okm.extend_from_slice(&t);
  }
  okm.truncate(l);
  okm
}
impl BlsPrivateKey {
  /// Generates a new BLS private key using the specified key material and parameters
  pub fn generate_from_ikm(
    ikm: &[u8],
    salt: &[u8],
    key_info: Option<&[u8]>,
  ) -> Result<Self, BlsError> {
    if ikm.len() < 32 {
      return Err(BlsError::Other("IKM must be at least 32 bytes".into()));
    }

    let mut ikm_with_zero = ikm.to_vec();
    ikm_with_zero.push(0u8); // I2OSP(0, 1)

    let mut current_salt = salt.to_vec();
    let key_info = key_info.unwrap_or(&[]);

    // Calculate L = ceil((3 * ceil(log2(r))) / 16)
    let r_bits = (PlutoScalarField::ORDER as f64).log2().ceil() as usize;
    let l = (3 * r_bits + 15) / 16;

    loop {
      // HKDF-Extract
      let prk = hkdf_extract(&current_salt, &ikm_with_zero);

      // Format key_info || I2OSP(L, 2)
      let mut info = key_info.to_vec();
      info.extend_from_slice(&(l as u16).to_be_bytes());

      // HKDF-Expand
      let okm = hkdf_expand(&prk, &info, l);

      // Convert to scalar and reduce mod r
      let sk_value = os2ip(&okm)
        .unwrap()
        .rem(&crypto_bigint::NonZero::new(U256::from(PlutoScalarField::ORDER as u64)).unwrap());

      if sk_value != U256::ZERO {
        return Ok(BlsPrivateKey {
          sk: PlutoScalarField::new(u64::from_be_bytes(
            sk_value.to_be_bytes()[24..32].try_into().unwrap(),
          ) as usize),
        });
      }

      // Update salt and try again
      let mut hasher = Sha256::new();
      hasher.update(&current_salt);
      current_salt = hasher.finalize().to_vec();
    }
  }

  // Keep the random generation as an alternative method
  pub fn generate_random<R: Rng>(rng: &mut R) -> Self {
    let sk = PlutoScalarField::new(rng.gen_range(1..=PlutoScalarField::ORDER));
    BlsPrivateKey { sk }
  }

  /// Returns the corresponding BLS public key.
  pub fn public_key(&self) -> BlsPublicKey {
    // Calculate public key as sk * G, where G is the generator of the subgroup.
    let pk = AffinePoint::<PlutoExtendedCurve>::GENERATOR * self.sk;
    BlsPublicKey { pk }
  }

  /// Signs a message using the BLS private key.
  ///
  /// The signature is computed as sk * H(m), where H is a hash-to-curve function.
  pub fn sign(&self, msg: &[u8]) -> Result<BlsSignature, BlsError> {
    let hash_point = hash_to_curve(msg)?;
    let sig_point = hash_point * self.sk;
    Ok(BlsSignature { sig: sig_point })
  }
}

impl BlsPublicKey {
  /// Verifies a BLS signature against the given message.
  ///
  /// The verification check uses the bilinear pairing:
  ///   e(signature, G) == e(H(message), public_key)
  pub fn verify(&self, msg: &[u8], signature: &BlsSignature) -> Result<(), BlsError> {
    // Step 3: Validate the public key
    self.validate()?;

    // Step 2: Check signature is in correct subgroup
    let subgroup_order = 17;
    if (signature.sig * PlutoScalarField::new(subgroup_order))
      != AffinePoint::<PlutoExtendedCurve>::Infinity
    {
      return Err(BlsError::InvalidSignature);
    }

    // Step 5-6: Hash message to point
    let hash_point = hash_to_curve(msg)?;

    // Steps 7-9: Pairing checks
    let left = pairing::<PlutoExtendedCurve, 17>(
      signature.sig,
      AffinePoint::<PlutoExtendedCurve>::GENERATOR,
    );
    let right = pairing::<PlutoExtendedCurve, 17>(hash_point, self.pk);

    if left == right {
      Ok(())
    } else {
      Err(BlsError::VerificationFailed)
    }
  }

  /// Validates a BLS public key according to the spec
  pub fn validate(&self) -> Result<(), BlsError> {
    // Check if point is valid (implicitly done by AffinePoint type)

    // Check if point is identity element
    if self.pk == AffinePoint::<PlutoExtendedCurve>::Infinity {
      return Err(BlsError::InvalidPublicKey);
    }

    // Check if point is in the correct subgroup
    let subgroup_order = 17;
    if (self.pk * PlutoScalarField::new(subgroup_order))
      != AffinePoint::<PlutoExtendedCurve>::Infinity
    {
      return Err(BlsError::InvalidPublicKey);
    }

    Ok(())
  }
}

impl BlsSignature {
  /// Aggregates multiple BLS signatures into a single signature.
  ///
  /// This function sums the individual signature points. All signatures must be on the same
  /// message.
  pub fn aggregate(signatures: &[BlsSignature]) -> Result<BlsSignature, BlsError> {
    if signatures.is_empty() {
      return Err(BlsError::Other("No signatures to aggregate".into()));
    }
    let mut agg = signatures[0].sig;
    for sig in signatures.iter().skip(1) {
      agg += sig.sig;
    }
    Ok(BlsSignature { sig: agg })
  }
}

/// Verifies an aggregated BLS signature for a single common message.
///
/// For aggregated signatures the verification check is:
///   e(aggregated_signature, G) == e(H(message), ∑ public_keys)
pub fn verify_aggregated_signature(
  pks: &[BlsPublicKey],
  messages: &[&[u8]],
  aggregated_sig: &BlsSignature,
) -> Result<(), BlsError> {
  // Precondition check
  if pks.is_empty() || pks.len() != messages.len() {
    return Err(BlsError::Other("Invalid number of public keys or messages".into()));
  }

  // Step 2-3: Validate signature and check subgroup
  let subgroup_order = 17;
  if (aggregated_sig.sig * PlutoScalarField::new(subgroup_order))
    != AffinePoint::<PlutoExtendedCurve>::Infinity
  {
    return Err(BlsError::InvalidSignature);
  }

  // Steps 4-9: Compute product of pairings
  let mut c1 = pairing::<PlutoExtendedCurve, 17>(
    AffinePoint::<PlutoExtendedCurve>::Infinity,
    AffinePoint::<PlutoExtendedCurve>::Infinity,
  );

  for (pk, msg) in pks.iter().zip(messages.iter()) {
    // Step 6: Validate each public key
    pk.validate()?;

    // Step 8: Hash message to point
    let q = hash_to_curve(msg)?;

    // Step 9: Accumulate pairing
    c1 = c1 * pairing::<PlutoExtendedCurve, 17>(q, pk.pk);
  }

  // Steps 10-11: Final pairing and comparison
  let c2 = pairing::<PlutoExtendedCurve, 17>(
    aggregated_sig.sig,
    AffinePoint::<PlutoExtendedCurve>::GENERATOR,
  );

  if c1 == c2 {
    Ok(())
  } else {
    Err(BlsError::VerificationFailed)
  }
}

/// Add this helper function
fn canonicalize<F>(x: F) -> F
where F: Field + Clone + std::ops::Neg<Output = F> + PartialOrd {
  let neg = -x.clone();
  // Compare the first coefficient of the field element
  if x > neg {
    neg
  } else {
    x
  }
}

/// Implements hash_to_field as specified in the standard
fn hash_to_field(msg: &[u8], count: usize) -> Vec<PlutoBaseField> {
  let mut result = Vec::with_capacity(count);
  for i in 0..count {
    let mut hasher = Sha256::new();
    hasher.update(msg);
    hasher.update(&(i as u32).to_be_bytes());
    let hash_result = hasher.finalize();

    let x_bytes: [u8; 8] = hash_result[0..8].try_into().unwrap();
    let x_val = u64::from_be_bytes(x_bytes);
    result.push(PlutoBaseField::from(x_val));
  }
  result
}

/// Implements map_to_curve as specified in the standard
fn map_to_curve(u: PlutoBaseField) -> AffinePoint<PlutoExtendedCurve> {
  let x = u;
  let x3 = x * x * x;
  let y2 = x3 + PlutoBaseField::from(3u64);

  if let Some(sqrt_result) = y2.sqrt() {
    let y = canonicalize(sqrt_result.0);
    AffinePoint::<PlutoExtendedCurve>::new(x.into(), y.into())
  } else {
    AffinePoint::<PlutoExtendedCurve>::Infinity
  }
}

/// Implements clear_cofactor as specified in the standard
fn clear_cofactor(point: AffinePoint<PlutoExtendedCurve>) -> AffinePoint<PlutoExtendedCurve> {
  let subgroup_order = 17;
  point * PlutoScalarField::new(subgroup_order)
}

/// Implements hash_to_curve as specified in the standard
fn hash_to_curve(msg: &[u8]) -> Result<AffinePoint<PlutoExtendedCurve>, BlsError> {
  // 1. Get two field elements
  let u = hash_to_field(msg, 2);

  // 2-3. Map both to curve points
  let q0 = map_to_curve(u[0]);
  let q1 = map_to_curve(u[1]);

  // 4. Add the points
  let r = q0 + q1;

  // 5. Clear the cofactor
  let p = clear_cofactor(r);

  // 6. Ensure point is valid and not identity
  if p == AffinePoint::<PlutoExtendedCurve>::Infinity {
    return Err(BlsError::HashToCurveFailed);
  }

  Ok(p)
}

#[cfg(test)]
mod tests {
  use rand::thread_rng;

  use super::*;

  /// Test that a valid signature verifies correctly.
  #[test]
  fn test_sign_and_verify() {
    let msg = b"Hello, BLS!";
    let mut rng = thread_rng();
    let sk = BlsPrivateKey::generate_random(&mut rng);
    let pk = sk.public_key();
    let sig = sk.sign(msg).expect("Signing should succeed");

    assert!(pk.verify(msg, &sig).is_ok(), "Valid signature should verify correctly");
  }

  /// Test that the signature for an empty message verifies correctly.
  #[test]
  fn test_empty_message() {
    let msg = b"";
    let mut rng = thread_rng();
    let sk = BlsPrivateKey::generate_random(&mut rng);
    let pk = sk.public_key();
    let sig = sk.sign(msg).expect("Signing an empty message should succeed");
    assert!(pk.verify(msg, &sig).is_ok(), "Signature for an empty message should verify correctly");
  }

  /// Test that tampering with a valid signature causes verification to fail.
  #[test]
  fn test_invalid_signature() {
    let msg = b"Test message";
    let mut rng = thread_rng();
    let sk = BlsPrivateKey::generate_random(&mut rng);
    let pk = sk.public_key();
    // Create a valid signature.
    let sig = sk.sign(msg).expect("Signing should succeed");
    // Tamper with the signature by adding the generator point.
    let tampered_sig = BlsSignature { sig: sig.sig + AffinePoint::<PlutoExtendedCurve>::GENERATOR };
    assert!(pk.verify(msg, &tampered_sig).is_err(), "Tampered signature should fail verification");
  }

  /// Test that aggregating multiple signatures on the same message verifies correctly.
  #[test]
  fn test_aggregate_signatures() {
    let msg = b"Aggregate Test Message";
    let mut rng = thread_rng();

    let mut signatures = Vec::new();
    let mut public_keys = Vec::new();

    // Generate several keypairs and corresponding signatures.
    for _ in 0..4 {
      let sk = BlsPrivateKey::generate_random(&mut rng);
      public_keys.push(sk.public_key());
      signatures.push(sk.sign(msg).expect("Signing should succeed"));
    }

    // Aggregate the signatures and verify the aggregated signature.
    let aggregated_signature =
      BlsSignature::aggregate(&signatures).expect("Aggregation should succeed");
    assert!(
      verify_aggregated_signature(&public_keys, &[msg], &aggregated_signature).is_ok(),
      "Aggregated signature should verify correctly"
    );
  }

  /// Test that trying to aggregate an empty slice of signatures produces an error.
  #[test]
  fn test_aggregate_empty_signatures() {
    let res = BlsSignature::aggregate(&[]);
    assert!(res.is_err(), "Aggregating an empty signature list should return an error");
  }

  /// Test that verifying an aggregated signature with an empty public key list fails.
  #[test]
  fn test_verify_aggregated_empty_public_keys() {
    let msg = b"Aggregate with Empty Public Keys";
    let mut rng = thread_rng();
    let sk = BlsPrivateKey::generate_random(&mut rng);
    let sig = sk.sign(msg).expect("Signing should succeed");
    let res = verify_aggregated_signature(&[], &[msg], &sig);
    assert!(res.is_err(), "Verification with an empty public key list should fail");
  }
}
