//! Tripartite Elliptic Curve Diffie Hellman Key Exchange Algorithm.
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

/// Compute a local pair of elliptic curve points to transmit.
///
/// The Single-Round, Tripartite Diffie-Hellman Key Exchange protocol requires each party to
/// transmit a point from both the base curve `p_a` and the extended curve `q_a`. This function
/// computes each from a local secret `d_a`.
///
/// ## Arguments
///
/// * `d_a` - The local secret.
///
/// ## Returns
///
/// A tuple containing the computed points `(p_a, q_a)`.
pub fn compute_local_pair(
  d_a: PlutoScalarField,
) -> (AffinePoint<PlutoBaseCurve>, AffinePoint<PlutoExtendedCurve>) {
  let p_a = AffinePoint::<PlutoBaseCurve>::GENERATOR * d_a;

  let q_a = AffinePoint::<PlutoExtendedCurve>::GENERATOR * d_a;

  (p_a, q_a)
}

/// Compute a shared secret from a local secret `d_a` and two foreign elliptic curve points `p_b`
/// and `q_c`.
///
/// The protocol relies on the bilinearity of the pairing function as well as modular exponentiation
/// to compute the shared sercret. We first compute the pairing with the input points, then
/// exponentate the result to the power of the local secret `d_a`.
///
/// ## Arguments
///
/// * `d_a` - The local secret.
/// * `p_b` - The foreign point on the base curve.
/// * `q_c` - The foreign point on the extended curve.
///
/// ## Returns
///
/// The computed shared secret on the Pluto extension field.
///
/// ## Panics
///
/// Panics under the conditions of the underlying pairing function, [`pairing`].
///
/// ## Notes
///
/// The order of points does not matter, only that the first point is on the base curve and the
/// second point is on the extended curve. That is to say, given two pairs of points, `(p_b, q_b)`
/// and `(q_c, p_c)`, this function may be called with either `(p_b, q_c)` or `(p_c, q_b)`.
pub fn compute_shared_secret(
  d_a: <PlutoBaseCurve as EllipticCurve>::ScalarField,
  p_b: AffinePoint<PlutoBaseCurve>,
  q_c: AffinePoint<PlutoExtendedCurve>,
) -> PlutoBaseFieldExtension {
  let p_b = AffinePoint::<PlutoExtendedCurve>::from(p_b);

  let pairing = pairing::<_, { PlutoBaseCurve::ORDER }>(p_b, q_c);

  let shared_secret = pairing.pow(d_a.value);

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
  fn test_compute_local_pair() {
    let mut rng = rand::rngs::OsRng;

    let d_a = PlutoScalarField::new(rand::Rng::gen_range(&mut rng, 1..=PlutoScalarField::ORDER));

    let (p_a, q_a) = compute_local_pair(d_a);

    assert_eq!(p_a, AffinePoint::<PlutoBaseCurve>::GENERATOR * d_a);
    assert_eq!(q_a, AffinePoint::<PlutoExtendedCurve>::GENERATOR * d_a);
  }

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
