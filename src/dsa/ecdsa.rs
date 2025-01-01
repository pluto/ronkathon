//! ECDSA signature verification
use std::hash::{DefaultHasher, Hasher};

use super::*;
use crate::{algebra::field::FiniteField, curve::CurveGroup};

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
pub fn sign<F: FiniteField, G: CurveGroup<Scalar = F>>(message: &[u8], private_key: F) -> (F, F) {
  // Hash and extract bits
  let bit_count = (F::ORDER.leading_zeros() - 1) as usize;
  let z = hash_and_extract_bits::<F>(message, bit_count);

  let mut rng = rand::rngs::OsRng;
  // Select a cryptographically secure random integer k from [1, n-1].
  let k = F::from(rand::Rng::gen_range(&mut rng, 1..=F::ORDER));

  // Compute the curve point (x_1, y_1) = k × G.
  let point = G::GENERATOR * k;
  let (mut x_1, _, is_infty) = point.xy();
  if is_infty {
    x_1 = G::BaseField::ZERO;
  }
  // Compute r = x_1 mod n. If r = 0, go back to step 3.
  let r = F::from(x_1.into());
  if r == F::ZERO {
    return sign::<F, G>(message, private_key);
  }
  // Compute s = k^(-1) (z + r * d_A) mod n. If s = 0, go back to step 3.
  let k_inv = k.inverse().unwrap();
  let s = k_inv * (z + r * private_key);
  if s == F::ZERO {
    return sign::<F, G>(message, private_key);
  }
  //  The signature is the pair (Notable not nessisarily a point on the curve) (r, s). the pair
  //    (r, -s mod n) is also a valid signature.
  // let r = F::from(r.value);
  // let s = F::from(s.value);
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
pub fn verify<F: FiniteField, G: CurveGroup<Scalar = F>>(
  m: &[u8],
  q_a: G,
  signature: (F, F),
) -> bool {
  // Check that n × Q_A = O.
  let (_, _, is_infty) = (q_a * F::ORDER.into()).xy();
  if !is_infty {
    return false;
  }

  // Verify that the signature is valid.
  let (r, s): (F, F) = signature;
  // Verify that r and s are integers in the interval [1, n-1].
  if r == F::ZERO || s == F::ZERO {
    return false;
  }
  // Hash and extract bits
  let bit_count = (F::ORDER.leading_zeros() - 1) as usize;
  let z = hash_and_extract_bits::<F>(m, bit_count);
  // Compute u_1 = zs^(-1) mod n.
  let s_inv = s.inverse().unwrap();
  let u_1 = z * s_inv;
  // Compute u_2 = rs^(-1) mod n.
  let u_2 = r * s_inv;
  // Compute the curve point (x_1, y_1) = u_1 × G + u_2 × Q_A. If
  let point = (G::GENERATOR * u_1) + (q_a * u_2);
  let (x_1, _, is_infty) = point.xy();
  if is_infty {
    panic!("signature invalid");
  }
  let x = F::from(x_1.into());
  r == x
}

/// Computes the hash of a message and extracts the leftmost bits.
fn hash_and_extract_bits<F: Field>(m: &[u8], bit_count: usize) -> F {
  let mut hasher = DefaultHasher::new();
  m.hash(&mut hasher);
  let e = hasher.finish().to_be_bytes();
  // let e_4_bytes = [e[0], e[1], e[2], e[3]];
  F::from(usize::from_be_bytes(e) & ((1 << bit_count) - 1))
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::algebra::{field::prime::PlutoScalarField, group::FiniteCyclicGroup, Finite};

  #[test]
  fn test_sign_verify() {
    // secret key
    let mut rng = rand::rngs::OsRng;
    let s_key = PlutoScalarField::new(rand::Rng::gen_range(&mut rng, 1..=PlutoScalarField::ORDER));

    // public key
    let q_a = AffinePoint::<PlutoBaseCurve>::GENERATOR * s_key;
    let m = b"Hello, world!";
    // sign the message
    let signature = sign::<PlutoScalarField, AffinePoint<PlutoBaseCurve>>(m, s_key);
    println!("signature = {:?}", signature);
    assert!(verify(m, q_a, signature));
  }
  #[test]
  fn test_invalid_signature() {
    // secret key
    let mut rng = rand::rngs::OsRng;
    let s_key = PlutoScalarField::new(rand::Rng::gen_range(&mut rng, 1..=PlutoScalarField::ORDER));
    // public key
    let q_a = AffinePoint::<PlutoBaseCurve>::GENERATOR * s_key;
    let m = b"Hello, Pluto!";
    // sign the message
    let mut signature = sign::<PlutoScalarField, AffinePoint<PlutoBaseCurve>>(m, s_key);
    // Modify the signature to make it invalid
    signature.0 = PlutoScalarField::ZERO; // Invalidate r
    assert!(!verify(m, q_a, signature), "Signature should be invalid but was verified as valid.");
  }
}
