//! Tripartite ECDH Key Exchange Algorithm.
use crate::{
  algebra::{
    field::{extension::PlutoBaseFieldExtension, prime::PlutoScalarField, Field},
    group::FiniteCyclicGroup,
  },
  curve::{
    pairing::pairing,
    pluto_curve::{PlutoBaseCurve, PlutoExtendedCurve},
    AffinePoint, EllipticCurve,
  },
};

// PARAMETERS
// *******************************************
// CURVE	the elliptic curve field and equation used
// P	    the generator point on the base curve
// Q	    the generator point on the extended curve
// d_A      the local secret
// d_B      the remote secret of B (unknown to the local party)
// d_C      the remote secret of C (unknown to the local party)
// P_A      the public key d_a × G = P_A (point on the base curve)
// P_B      the public key d_b × G = P_B (point on the base curve)
// P_C      the public key d_c × G = P_C (point on the base curve)
// Q_A      the public key d_a × G = Q_A (point on the extended curve)
// Q_B      the public key d_b × G = Q_B (point on the extended curve)
// Q_C      the public key d_c × G = Q_C (point on the extended curve)

/// COMPUTE LOCAL PAIR
/// *******************************************
/// 1. Compute P_A = d_A × P
/// 2. Compute Q_A = d_A × Q
pub fn compute_local_pair(
  local_secret: PlutoScalarField,
) -> (AffinePoint<PlutoBaseCurve>, AffinePoint<PlutoExtendedCurve>) {
  let p_a = AffinePoint::<PlutoBaseCurve>::GENERATOR * local_secret;

  let q_a = AffinePoint::<PlutoExtendedCurve>::GENERATOR * local_secret;

  (p_a, q_a)
}

/// COMPUTE SHARED SECRET
/// *******************************************
/// 1. Transform p_b to extension curve type
/// 2. Compute pairing of the two foreign points
/// 3. Compute shared secret
pub fn compute_shared_secret(
  local_secret: <PlutoBaseCurve as EllipticCurve>::ScalarField,
  p_b: AffinePoint<PlutoBaseCurve>,
  q_c: AffinePoint<PlutoExtendedCurve>,
) -> PlutoBaseFieldExtension {
  let p_b = AffinePoint::<PlutoExtendedCurve>::from(p_b);

  let pairing = pairing::<_, { PlutoBaseCurve::ORDER }>(p_b, q_c);

  let shared_secret = pairing.pow(local_secret.value);

  shared_secret
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    algebra::{field::prime::PlutoScalarField, group::FiniteCyclicGroup, Finite},
    curve::{pluto_curve::PlutoBaseCurve, AffinePoint},
  };

  #[test]
  fn test_compute_tripartite_shared_secret() {
    let mut rng = rand::rngs::OsRng;

    let p = AffinePoint::<PlutoBaseCurve>::GENERATOR;
    let q = AffinePoint::<PlutoExtendedCurve>::GENERATOR;

    let d_a = PlutoScalarField::new(rand::Rng::gen_range(&mut rng, 1..PlutoScalarField::ORDER));
    let d_b = PlutoScalarField::new(rand::Rng::gen_range(&mut rng, 1..PlutoScalarField::ORDER));
    let d_c = PlutoScalarField::new(rand::Rng::gen_range(&mut rng, 1..PlutoScalarField::ORDER));

    let p_a = p * d_a;
    let p_b = p * d_b;
    let p_c = p * d_c;

    let q_a = q * d_a;
    let q_b = q * d_b;
    let q_c = q * d_c;

    let shared_secret_a0 = compute_shared_secret(d_a, p_b, q_c);
    let shared_secret_a1 = compute_shared_secret(d_a, p_c, q_b);
    let shared_secret_b0 = compute_shared_secret(d_b, p_c, q_a);
    let shared_secret_b1 = compute_shared_secret(d_b, p_a, q_c);
    let shared_secret_c0 = compute_shared_secret(d_c, p_a, q_b);
    let shared_secret_c1 = compute_shared_secret(d_c, p_b, q_a);

    assert_eq!(shared_secret_a0, shared_secret_a1);
    assert_eq!(shared_secret_b0, shared_secret_b1);
    assert_eq!(shared_secret_c0, shared_secret_c1);
    assert_eq!(shared_secret_a0, shared_secret_b0);
    assert_eq!(shared_secret_a0, shared_secret_c0);
  }
}
