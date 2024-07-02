//! ECDSA signature verification
use std::hash::{DefaultHasher, Hasher};

use self::field::prime::PlutoScalarField;
use super::*;

// PARAMETERS
// *******************************************
// CURVE	the elliptic curve field and equation used
// G	    a point on the curve that generates a subgroup of large prime order n
// n	    integer order of G, means that n × G = O, n must also be prime.
// d_A	    the private key (randomly selected) (scaler in F_n)
// Q_A	    the public key d_a × G = Q_A (point on the curve)
// m	    the message to send

/// SIGNING ALGORITHM
/// *******************************************
/// 1. Compute e = HASH(m), where HASH is a cryptographic hash function.
/// 2. Let z be the L_n leftmost bits of e, where L_n is the bit length of the group order n.
/// 3. Select a cryptographically secure random integer k from [1, n-1].
/// 4. Compute the curve point (x_1, y_1) = k × G.
/// 5. Compute r = x_1 mod n. If r = 0, go back to step 3.
/// 6. Compute s = k^(-1) (z + r * d_A) mod n. If s = 0, go back to step 3.
/// 7. The signature is the pair (r, s). the pair (r, -s mod n) is also a valid signature.
pub fn sign(message: &[u8], private_key: PlutoScalarField) -> (PlutoScalarField, PlutoScalarField) {
  // Hash and extract bits
  let z = hash_and_extract_bits(message, 17);

  let mut rng = rand::rngs::OsRng;
  // Select a cryptographically secure random integer k from [1, n-1].
  let k = PlutoScalarField::new(rand::Rng::gen_range(&mut rng, 1..=PlutoScalarField::ORDER));

  // Compute the curve point (x_1, y_1) = k × G.
  let point = AffinePoint::<PlutoBaseCurve>::generator() * k;
  let x_1 = match point {
    AffinePoint::Point(x, _) => x,
    _ => PlutoBaseField::ZERO,
  };
  // Compute r = x_1 mod n. If r = 0, go back to step 3.
  let r = PlutoScalarField::from(x_1.value);
  if r == PlutoScalarField::ZERO {
    return sign(message, private_key);
  }
  // Compute s = k^(-1) (z + r * d_A) mod n. If s = 0, go back to step 3.
  let k_inv = k.inverse().unwrap();
  let s = k_inv * (z + r * private_key);
  if s == PlutoScalarField::ZERO {
    return sign(message, private_key);
  }
  //  The signature is the pair (Notable not nessisarily a point on the curve) (r, s). the pair
  //    (r, -s mod n) is also a valid signature.
  let r = PlutoScalarField::from(r.value);
  let s = PlutoScalarField::from(s.value);
  (r, s)
}

/// SIGNATURE VERIFICATION ALGORITHM
/// *******************************************
/// Check that public key Q_A is a valid point on the curve.
/// 1. Check that Q_A != O.
/// 2. Check that x_Q_A and y_Q_A are integers in the interval [0, p-1].
/// 3. Check that n × Q_A = O.
///
/// Verify that the signature is valid.
/// 1. Verify that r and s are integers in the interval [1, n-1].
/// 2. Compute e = HASH(m).
/// 3. Let z be the L_n leftmost bits of e.
/// 4. Compute u_1 = zs^(-1) mod n.
/// 5. Compute u_2 = rs^(-1) mod n.
/// 6. Compute the curve point (x_1, y_1) = u_1 × G + u_2 × Q_A. If = O, the signature is invalid.
/// 7. The signature is valid if r = x_1 mod n, invalid otherwise.
pub fn verify(
  m: &[u8],
  q_a: AffinePoint<PlutoBaseCurve>,
  signature: (PlutoScalarField, PlutoScalarField),
) -> bool {
  // Check that n × Q_A = O.
  if (q_a * 17) != AffinePoint::Infinity {
    return false;
  }

  // Verify that the signature is valid.
  let (r, s): (PlutoScalarField, PlutoScalarField) = signature;
  // Verify that r and s are integers in the interval [1, n-1].
  if r == PlutoScalarField::ZERO || s == PlutoScalarField::ZERO {
    return false;
  }
  // Hash and extract bits
  let z = hash_and_extract_bits(m, 17);
  // Compute u_1 = zs^(-1) mod n.
  let s_inv = s.inverse().unwrap();
  let u_1 = z * s_inv;
  // Compute u_2 = rs^(-1) mod n.
  let u_2 = r * s_inv;
  // Compute the curve point (x_1, y_1) = u_1 × G + u_2 × Q_A. If
  let point = (AffinePoint::<PlutoBaseCurve>::generator() * u_1) + (q_a * u_2);
  let (x_1, _) = match point {
    AffinePoint::Point(x, y) => (x, y),
    _ => (PlutoBaseField::ZERO, PlutoBaseField::ZERO),
  };
  let x = PlutoScalarField::from(x_1.value);
  r == x
}

/// Computes the hash of a message and extracts the leftmost bits.
fn hash_and_extract_bits(m: &[u8], bit_count: usize) -> PlutoScalarField {
  let mut hasher = DefaultHasher::new();
  m.hash(&mut hasher);
  let e = hasher.finish().to_be_bytes();
  let e_4_bytes = [e[0], e[1], e[2], e[3]];
  PlutoScalarField::from(u32::from_be_bytes(e_4_bytes) >> (32 - bit_count))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_sign_verify() {
    // secret key
    let mut rng = rand::rngs::OsRng;
    let s_key = PlutoScalarField::new(rand::Rng::gen_range(&mut rng, 1..=PlutoScalarField::ORDER));

    // public key
    let q_a = AffinePoint::<PlutoBaseCurve>::generator() * s_key;
    let m = b"Hello, world!";
    // sign the message
    let signature = sign(m, s_key);
    println!("signature = {:?}", signature);
    assert!(verify(m, q_a, signature));
  }
  #[test]
  fn test_invalid_signature() {
    // secret key
    let mut rng = rand::rngs::OsRng;
    let s_key = PlutoScalarField::new(rand::Rng::gen_range(&mut rng, 1..=PlutoScalarField::ORDER));
    // public key
    let q_a = AffinePoint::<PlutoBaseCurve>::generator() * s_key;
    let m = b"Hello, Pluto!";
    // sign the message
    let mut signature = sign(m, s_key);
    // Modify the signature to make it invalid
    signature.0 = PlutoScalarField::ZERO; // Invalidate r
    assert!(!verify(m, q_a, signature), "Signature should be invalid but was verified as valid.");
  }
}
