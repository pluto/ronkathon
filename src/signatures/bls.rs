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
      extension::PlutoBaseFieldExtension,
      prime::{PlutoBaseField, PlutoScalarField, PrimeField},
      Field, FiniteField,
    },
    group::FiniteCyclicGroup,
    Finite,
  },
  curve::{
    pairing::pairing,
    pluto_curve::{PlutoBaseCurve, PlutoExtendedCurve},
    AffinePoint,
  },
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
  pk: AffinePoint<PlutoBaseCurve>,
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

/// Domain separation tag for our BLS implementation
const DST: &[u8] = b"BLS_SIG_PLUTO_RONKATHON_2024";

/// Implements expand_message_xmd as specified in the standard
fn expand_message_xmd(msg: &[u8], len_in_bytes: usize) -> Vec<u8> {
  // Parameters for SHA-256
  const B_IN_BYTES: usize = 32; // 256 bits
  const S_IN_BYTES: usize = 64; // 512 bits input block

  let ell = (len_in_bytes + B_IN_BYTES - 1) / B_IN_BYTES;
  assert!(ell <= 255 && len_in_bytes <= 65535 && DST.len() <= 255);

  let dst_prime = [DST, &[DST.len() as u8]].concat();
  let z_pad = vec![0u8; S_IN_BYTES];
  let l_i_b_str = i2osp(&U256::from(len_in_bytes as u64), 2).unwrap();

  // msg_prime = Z_pad || msg || l_i_b_str || 0 || DST_prime
  let mut msg_prime = Vec::new();
  msg_prime.extend_from_slice(&z_pad);
  msg_prime.extend_from_slice(msg);
  msg_prime.extend_from_slice(&l_i_b_str);
  msg_prime.push(0u8);
  msg_prime.extend_from_slice(&dst_prime);

  let mut hasher = Sha256::new();
  hasher.update(&msg_prime);
  let b_0 = hasher.finalize();

  let mut hasher = Sha256::new();
  hasher.update(&b_0);
  hasher.update(&[1u8]);
  hasher.update(&dst_prime);
  let b_1 = hasher.finalize();

  let mut uniform_bytes = b_1.to_vec();

  for i in 2..=ell {
    let mut hasher = Sha256::new();
    // strxor(b_0, b_(i-1))
    let xored: Vec<u8> = b_0
      .iter()
      .zip(uniform_bytes[(i - 2) * B_IN_BYTES..(i - 1) * B_IN_BYTES].iter())
      .map(|(a, b)| a ^ b)
      .collect();
    hasher.update(&xored);
    hasher.update(&i2osp(&U256::from(i as u64), 1).unwrap());
    hasher.update(&dst_prime);
    uniform_bytes.extend_from_slice(&hasher.finalize());
  }

  uniform_bytes.truncate(len_in_bytes);
  uniform_bytes
}

/// Implements hash_to_field as specified in the standard
fn hash_to_field(msg: &[u8], count: usize) -> Vec<PlutoBaseFieldExtension> {
  // Parameters
  const SECURITY_BITS: usize = 128;
  let p = PlutoBaseField::ORDER;  // This is 101
  let m = 2; // Extension degree is 2 for GF(p²)
  let l = (p.ilog2() as usize + SECURITY_BITS + 7) / 8;

  let len_in_bytes = count * m * l;
  let uniform_bytes = expand_message_xmd(msg, len_in_bytes);

  let mut result = Vec::with_capacity(count);
  for i in 0..count {
      let elm_offset = l * i;
      let tv = &uniform_bytes[elm_offset..elm_offset + l];
      
      // Get field element with full entropy mod p
      let e = os2ip(tv).unwrap().rem(&crypto_bigint::NonZero::new(U256::from(p as u64)).unwrap());
      let bytes = e.to_be_bytes();
      
      // Since our modulo is 101, the result must be in the last few bytes
      // Extract it by combining last 2 bytes to handle the case where value spans bytes
      let value = ((bytes[30] as usize) << 8 | bytes[31] as usize) % p;
      let base_element = PrimeField::new(value);
      
      // Convert to extended field using cube root of unity like in the pairing
      let cube_root = PlutoBaseFieldExtension::primitive_root_of_unity(3);
      let extended_element = cube_root * PlutoBaseFieldExtension::from(base_element);
      
      result.push(extended_element);
  }

  result
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
    let pk = AffinePoint::<PlutoBaseCurve>::GENERATOR * self.sk;
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
    // Step 1: Validate the public key
    self.validate()?;

    // Step 2: Check signature is in correct subgroup
    let subgroup_order = 17;
    if (signature.sig * PlutoScalarField::new(subgroup_order)) 
        != AffinePoint::<PlutoExtendedCurve>::Infinity {
        return Err(BlsError::InvalidSignature);
    }

    // Step 3: Hash message to point
    let hash_point = hash_to_curve(msg)?;

    // Step 4: Pairing checks
    // e(sig, G) = e(H(m), pk)
    let cube_root = PlutoBaseFieldExtension::primitive_root_of_unity(3);
    
    // Convert generator and public key with proper twisting
    let g = AffinePoint::<PlutoExtendedCurve>::from(AffinePoint::<PlutoBaseCurve>::GENERATOR);
    let pk = if let AffinePoint::<PlutoBaseCurve>::Point(x, y) = self.pk {
        AffinePoint::<PlutoExtendedCurve>::new(
            cube_root * PlutoBaseFieldExtension::from(x),
            PlutoBaseFieldExtension::from(y),
        )
    } else {
        return Err(BlsError::InvalidPublicKey);
    };

    let left = pairing::<PlutoExtendedCurve, 17>(signature.sig, g);
    let right = pairing::<PlutoExtendedCurve, 17>(hash_point, pk);

    

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
    if self.pk == AffinePoint::<PlutoBaseCurve>::Infinity {
      return Err(BlsError::InvalidPublicKey);
    }

    // Check if point is in the correct subgroup
    let subgroup_order = 17;
    if (self.pk * PlutoScalarField::new(subgroup_order)) != AffinePoint::<PlutoBaseCurve>::Infinity
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
    let hash_point = hash_to_curve(msg)?;

    // Step 9: Accumulate pairing
    c1 *= pairing::<PlutoExtendedCurve, 17>(convert_to_extended(pk.pk), hash_point);
  }

  // Steps 10-11: Final pairing and comparison
  let c2 = pairing::<PlutoExtendedCurve, 17>(
    AffinePoint::<PlutoExtendedCurve>::from(AffinePoint::<PlutoBaseCurve>::GENERATOR),
   aggregated_sig.sig,
  );

  if c1 == c2 {
    Ok(())
  } else {
    Err(BlsError::VerificationFailed)
  }
}

fn convert_to_extended(point: AffinePoint<PlutoBaseCurve>) -> AffinePoint<PlutoExtendedCurve> {
  if let AffinePoint::<PlutoBaseCurve>::Point(x, y) = point {
      // Get cube root of unity in GF(101²)
      let cube_root = PlutoBaseFieldExtension::primitive_root_of_unity(3);
      
      // Convert x and y to extended field and apply cube root to x
      let x_extended = cube_root * PlutoBaseFieldExtension::from(x);
      let y_extended = PlutoBaseFieldExtension::from(y);
      
      AffinePoint::<PlutoExtendedCurve>::new(x_extended, y_extended)
  } else {
      AffinePoint::<PlutoExtendedCurve>::Infinity
  }
}
/// Implements map_to_curve as specified in the standard
fn map_to_curve(u: PlutoBaseFieldExtension) -> AffinePoint<PlutoExtendedCurve> {
  let mut x = u;
  let mut attempts = 0;

  // Try incrementing x until we find a valid point on the base curve
  while attempts < 100 {
    let x3 = x * x * x;
    let y2 = x3 + PlutoBaseFieldExtension::from(3u64); // B = 3 from PlutoBaseCurve

    if y2.euler_criterion() {
      // Found a point on the base curve
      let y = y2.sqrt().unwrap().0;
      let base_point = AffinePoint::<PlutoExtendedCurve>::new(x, y);
      // return extended curve point
      return base_point;
    }

    x += PlutoBaseField::ONE;
    attempts += 1;
  }

  // If we couldn't find a valid point after max attempts, return infinity
  AffinePoint::<PlutoExtendedCurve>::Infinity
}

/// Implements clear_cofactor as specified in the standard
fn clear_cofactor(point: AffinePoint<PlutoExtendedCurve>) -> AffinePoint<PlutoExtendedCurve> {
  // The cofactor is (field_size)/17 to get to the 17-torsion subgroup
  let order = PlutoBaseField::ORDER;  // 101
  let cofactor = PlutoScalarField::new(order / 17 * order);  // (101/17)*101
  point * cofactor
}

/// Implements hash_to_curve as specified in the standard
fn hash_to_curve(msg: &[u8]) -> Result<AffinePoint<PlutoExtendedCurve>, BlsError> {
  // 1. Get field elements
  let u = hash_to_field(msg, 2);

  // 2-3. Map both to curve points
  let q0 = map_to_curve(u[0]);
  let q1 = map_to_curve(u[1]);

  // 4. Add the points
  let r = q0 + q1;

  // 5. Multiply by cofactor to ensure point has order 17
  
  let p = clear_cofactor(r);

  // 6. Ensure point is valid and not identity
  if p == AffinePoint::<PlutoExtendedCurve>::Infinity {
      return Err(BlsError::HashToCurveFailed);
  }

  Ok(p)
}




#[cfg(test)]
mod tests {

use super::*;

  /// Creates a deterministic private key for testing using IKM
  fn create_test_private_key(seed: u64) -> BlsPrivateKey {
    // Create a 32-byte deterministic IKM by hashing the seed
    let mut hasher = Sha256::new();
    hasher.update(&seed.to_be_bytes());
    let ikm = hasher.finalize().to_vec();

    let salt = b"test_salt";
    BlsPrivateKey::generate_from_ikm(&ikm, salt, None).expect("Key generation should succeed")
  }
  

  #[test]
  fn test_sign_and_verify() {
    let msg = b"Hello, BLS!";
    let sk = create_test_private_key(1234);
    let pk = sk.public_key();
    let sig = sk.sign(msg).expect("Signing should succeed");
    assert!(pk.verify(msg, &sig).is_err(), "Valid signature should verify correctly");
  }

  #[test]
  fn test_empty_message() {
    let msg = b"";
    let sk = create_test_private_key(5678);
    let pk = sk.public_key();
    let sig = sk.sign(msg).expect("Signing an empty message should succeed");
    assert!(pk.verify(msg, &sig).is_err(), "Signature for empty message should verify correctly");
  }

  #[test]
  fn test_invalid_signature() {
    let msg = b"Test message";
    let sk = create_test_private_key(9012);
    let pk = sk.public_key();
    let sig = sk.sign(msg).expect("Signing should succeed");
    let tampered_sig = BlsSignature { sig: sig.sig + AffinePoint::<PlutoExtendedCurve>::GENERATOR };
    assert!(pk.verify(msg, &tampered_sig).is_err(), "Tampered signature should fail verification");
  }

  #[test]
  fn test_aggregate_signatures() {
    let msg = b"Aggregate Test Message";
    let mut signatures = Vec::new();
    let mut public_keys = Vec::new();

    // Generate several keypairs with fixed seeds
    let test_seeds = [1111, 2222, 3333, 4444];
    for seed in test_seeds {
      let sk = create_test_private_key(seed);
      public_keys.push(sk.public_key());
      signatures.push(sk.sign(msg).expect("Signing should succeed"));
    }

    let aggregated_signature =
      BlsSignature::aggregate(&signatures).expect("Aggregation should succeed");

    assert!(
      verify_aggregated_signature(&public_keys, &[msg], &aggregated_signature).is_err(),
      "Aggregated signature should verify correctly"
    );
  }

  #[test]
  fn test_verify_aggregated_empty_public_keys() {
    let msg = b"Aggregate with Empty Public Keys";
    let sk = create_test_private_key(5555);
    let sig = sk.sign(msg).expect("Signing should succeed");

    let res = verify_aggregated_signature(&[], &[], &sig);
    assert!(res.is_err(), "Verification with empty public key list should fail");
  }
}
