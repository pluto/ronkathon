//! ECDH Key Exchange Algorithm
use crate::{algebra::field::FiniteField, curve::CurveGroup};

// PARAMETERS
// *******************************************
// CURVE	the elliptic curve field and equation used
// G	    a point on the curve that generates a subgroup of large prime order n
// d_A      the local secret
// d_B      the remote secret (unknown to the local party)
// Q_A      the public key d_a × G = Q_A (point on the curve)
// Q_B      the public key d_b × G = Q_B (point on the curve)

/// COMPUTE SHARED SECRET
/// *******************************************
/// 1. Compute d_A × Q_B
pub fn compute_shared_secret<F: FiniteField, G: CurveGroup<Scalar = F>>(d_a: F, q_b: G) -> G {
  q_b * d_a
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    algebra::{field::prime::PlutoScalarField, group::FiniteCyclicGroup, Finite},
    curve::{pluto_curve::PlutoBaseCurve, AffinePoint},
  };

  #[test]
  fn test_compute_shared_secret() {
    let mut rng = rand::rngs::OsRng;

    let d_a = PlutoScalarField::new(rand::Rng::gen_range(&mut rng, 1..=PlutoScalarField::ORDER));
    let d_b = PlutoScalarField::new(rand::Rng::gen_range(&mut rng, 1..=PlutoScalarField::ORDER));

    let q_a = AffinePoint::<PlutoBaseCurve>::GENERATOR * d_a;
    let q_b = AffinePoint::<PlutoBaseCurve>::GENERATOR * d_b;

    let shared_secret_a = compute_shared_secret(d_a, q_b);
    let shared_secret_b = compute_shared_secret(d_b, q_a);

    assert_eq!(shared_secret_a, shared_secret_b);
  }
}
