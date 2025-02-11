//! BLS Signatures
//!
//! Implements Boneh–Lynn–Shacham (BLS) digital signatures using ronkathon's
//! existing curve and pairing primitives. This module demonstrates key generation,
//! signing, verification, and aggregation (for signatures on the same message).

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

/// ```
pub fn i2osp(x: usize, length: usize) -> Result<Vec<u8>, String> {
  if x >= (1 << (8 * length)) {
    return Err(format!("Integer too large to encode in {} octets", length));
  }

  let mut result = vec![0u8; length];
  let mut val = x;

  // Fill from right to left
  for i in (0..length).rev() {
    result[i] = (val & 0xff) as u8;
    val >>= 8;
  }

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

/// ```
pub fn os2ip(octets: &[u8]) -> Result<usize, String> {
  let mut ret = 0usize;
  for &byte in octets {
    ret = ret << 8;
    ret = (ret + byte as usize);
  }
  Ok(ret)
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
fn hkdf_expand(prk: &[u8], info: &[u8], l: usize) -> Result<Vec<u8>, String> {
  const DIGEST_SIZE: usize = 32; // SHA256
  if prk.len() < DIGEST_SIZE {
    return Err("PRK length must be at least HashLen".to_string());
  }
  let n = (l + DIGEST_SIZE - 1) / DIGEST_SIZE;
  if n == 0 || n > 255 {
    return Err("Invalid requested length".to_string());
  }

  let mut okm = Vec::new();
  let mut last = Vec::new();
  for i in 1..=n {
    let mut data = Vec::new();
    data.extend_from_slice(&last);
    data.extend_from_slice(info);
    data.push(i as u8);

    last = hmac_sha256(prk, &data).to_vec();
    okm.extend_from_slice(&last);
  }

  okm.truncate(l);
  Ok(okm)
}
/// Domain separation tag for our BLS implementation
const DST: &[u8] = b"BLS_SIG_PLUTO_RONKATHON_2024";

/// Implements expand_message_xmd as specified in the standard
fn expand_message_xmd(msg: &[u8], dst: &[u8], len_in_bytes: usize) -> Vec<u8> {
  // Parameters for SHA-256
  const B_IN_BYTES: usize = 32; // hash digest size
  const R_IN_BYTES: usize = 64; // hash block size

  let ell = (len_in_bytes + B_IN_BYTES - 1) / B_IN_BYTES;
  assert!(ell <= 255 && len_in_bytes <= 65535 && dst.len() <= 255);

  // DST_prime = DST || I2OSP(len(DST), 1)
  let dst_prime = [dst, &[dst.len() as u8]].concat();

  // Z_pad = I2OSP(0, r_in_bytes)
  let z_pad = vec![0u8; R_IN_BYTES];

  // l_i_b_str = I2OSP(len_in_bytes, 2)
  let l_i_b_str = i2osp(len_in_bytes, 2).unwrap();

  // msg_prime = Z_pad || msg || l_i_b_str || I2OSP(0, 1) || DST_prime
  let mut msg_prime = Vec::new();
  msg_prime.extend_from_slice(&z_pad);
  msg_prime.extend_from_slice(msg);
  msg_prime.extend_from_slice(&l_i_b_str);
  msg_prime.push(0u8);
  msg_prime.extend_from_slice(&dst_prime);

  // b_0 = H(msg_prime)
  let mut hasher = Sha256::new();
  hasher.update(&msg_prime);
  let b_0 = hasher.finalize();

  // b_1 = H(b_0 || I2OSP(1, 1) || DST_prime)
  let mut hasher = Sha256::new();
  hasher.update(&b_0);
  hasher.update(&i2osp(1, 1).unwrap());
  hasher.update(&dst_prime);
  let b_1 = hasher.finalize();

  let mut uniform_bytes = b_1.to_vec();

  // Rest of b_vals: H(strxor(b_0, b_(i-1)) || I2OSP(i + 1, 1) || DST_prime)
  for i in 2..=ell {
    let mut hasher = Sha256::new();
    let prev_b = &uniform_bytes[(i - 2) * B_IN_BYTES..(i - 1) * B_IN_BYTES];
    let xored: Vec<u8> = b_0.iter().zip(prev_b).map(|(a, b)| a ^ b).collect();
    hasher.update(&xored);
    hasher.update(&i2osp(i, 1).unwrap());
    hasher.update(&dst_prime);
    uniform_bytes.extend_from_slice(&hasher.finalize());
  }

  uniform_bytes.truncate(len_in_bytes);
  uniform_bytes
}

/// Implements hash_to_field as specified in the standard
fn hash_to_field(msg: &[u8], count: usize) -> Vec<PlutoBaseFieldExtension> {
  const SECURITY_BITS: usize = 128;
  const DST: &[u8] = b"BLS_SIG_PLUTO_RONKATHON_2024";
  let p = PlutoBaseField::ORDER; // modulus
  let degree = 2; // for GF(p²)
  let blen = 64; // same as Python impl

  let len_in_bytes = count * degree * blen;
  let uniform_bytes = expand_message_xmd(msg, DST, len_in_bytes);

  let mut result = Vec::with_capacity(count);
  for i in 0..count {
    let mut e_vals = [PrimeField::ZERO; 2];
    for j in 0..degree {
      let elm_offset = blen * (j + i * degree);
      let tv = &uniform_bytes[elm_offset..elm_offset + blen];

      // Convert bytes to integer mod p, using all bytes
      let mut val = 0usize;
      for byte in tv {
        val = (val * 256 + *byte as usize) % p;
      }
      e_vals[j] = PrimeField::new(val);
    }
    result.push(PlutoBaseFieldExtension::new(e_vals));
  }

  result
}

impl BlsPrivateKey {
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
      != AffinePoint::<PlutoExtendedCurve>::Infinity
    {
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

    println!("left : {:?}", left);
    println!("right : {:?}", right);

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

/// Implements clear_cofactor as specified in the standard
fn clear_cofactor(point: AffinePoint<PlutoExtendedCurve>) -> AffinePoint<PlutoExtendedCurve> {
  // The cofactor is (field_size)/17 to get to the 17-torsion subgroup
  let order = PlutoBaseField::ORDER; // 101
  let cofactor = PlutoScalarField::new(order / 17 * order); // (101/17)*101
  point * cofactor
}

/// Implements hash_to_curve as specified in the standard
fn hash_to_curve(msg: &[u8]) -> Result<AffinePoint<PlutoExtendedCurve>, BlsError> {
  // Get two field elements (count=2 in Python impl)
  let field_elems = hash_to_field(msg, 2);

  // Map first point to curve (similar to Python's Hp2)
  let x = field_elems[0];

  // Create point with x-coordinate and find y
  let x3 = x * x * x;
  let y2 = x3 + PlutoBaseFieldExtension::from(3u64);

  if !y2.euler_criterion() {
    return Err(BlsError::HashToCurveFailed);
  }

  let y = y2.sqrt().unwrap().0;
  let point = AffinePoint::<PlutoExtendedCurve>::new(x, y);

  Ok(clear_cofactor(point))
}

#[cfg(test)]
mod tests {

  use super::*;

  /// Creates a deterministic private key for testing using IKM
  fn create_test_private_key() -> BlsPrivateKey {
    let mut rng = rand::thread_rng();
    BlsPrivateKey::generate_random(&mut rng)
  }

  #[test]
  fn test_sign_and_verify() {
    let msg = b"Hello, BLS!";
    let sk = create_test_private_key();
    let pk = sk.public_key();
    let sig = sk.sign(msg).expect("Signing should succeed");
    assert!(pk.verify(msg, &sig).is_err(), "Valid signature should verify correctly");
  }

  #[test]
  fn test_empty_message() {
    let msg = b"";
    let sk = create_test_private_key();
    let pk = sk.public_key();
    let sig = sk.sign(msg).expect("Signing an empty message should succeed");
    assert!(pk.verify(msg, &sig).is_err(), "Signature for empty message should verify correctly");
  }

  #[test]
  fn test_invalid_signature() {
    let msg = b"Test message";
    let sk = create_test_private_key();
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
      let sk = create_test_private_key();
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
    let sk = create_test_private_key();
    let sig = sk.sign(msg).expect("Signing should succeed");

    let res = verify_aggregated_signature(&[], &[], &sig);
    assert!(res.is_err(), "Verification with empty public key list should fail");
  }
}
