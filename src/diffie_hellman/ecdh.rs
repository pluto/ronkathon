//! Elliptic Curve Diffie Hellman Key Exchange Algorithm
use crate::{algebra::field::FiniteField, curve::CurveGroup};

/// Compute a shared secret from a local secret `d_a` and a foreign elliptic curve point `q_b`.
///
/// ## Arguments
///
/// * `d_a` - The local secret.
/// * `q_b` - The foreign point on the curve.
///
/// ## Returns
///
/// The computed shared secret.
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
