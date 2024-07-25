//! Does the SRS setup for the KZG10 scheme.

use algebra::group::FiniteCyclicGroup;

use self::{curve::pairing::pairing, PlutoScalarField};
use super::*;

/// simple setup to get params.
#[allow(dead_code, clippy::type_complexity)]
pub fn setup() -> (Vec<AffinePoint<PlutoExtendedCurve>>, Vec<AffinePoint<PlutoExtendedCurve>>) {
  // NOTE: For demonstration purposes only.

  // This is just tau from plonk by hand, it is not actually secure
  let tau: PlutoScalarField = PlutoScalarField::new(2);

  let g1 = AffinePoint::<PlutoExtendedCurve>::from(AffinePoint::<PlutoBaseCurve>::GENERATOR);
  let g2 = AffinePoint::<PlutoExtendedCurve>::GENERATOR;
  // NOTE: Just sample the d of both for now.
  // - g1 and g2 SRS have variable sizes for diff kzg uses
  // - in eth blobs, g1 is 4096 elements, g2 is 16 elements
  // - in plonk, we need d+5 g1 elements and one g2 element
  let mut srs_g1_points: Vec<AffinePoint<PlutoExtendedCurve>> = vec![];
  let mut srs_g2_points: Vec<AffinePoint<PlutoExtendedCurve>> = vec![];
  for i in 0..7 {
    // G1 Group

    // degree seven commitment poly
    // g1srs = {g1^tau^0, g1^tau^1, g1^tau^2, g1^tau^3, g1^tau^4, g1^tau^5, g1^tau^6}
    let result = g1 * tau.pow(i);

    srs_g1_points.push(result);
    // G2 Group

    // degree two divisor poly
    if i < 2 {
      // g2srs = {g2^tau^0, g2^tau^1}
      let result = g2 * tau.pow(i);
      srs_g2_points.push(result);
    }
  }

  (srs_g1_points, srs_g2_points)
}

/// kzg poly commit
/// Both binding and hiding commitment
#[allow(dead_code)]
pub fn commit(
  coeffs: Vec<PlutoScalarField>,
  g1_srs: Vec<AffinePoint<PlutoExtendedCurve>>,
) -> AffinePoint<PlutoExtendedCurve> {
  // check srs is longer than coefs
  assert!(g1_srs.len() >= coeffs.len());
  // SUM_{i=0}^{n} (g1^tau^i * coef_i)
  g1_srs
    .into_iter()
    .zip(coeffs)
    .map(|(g1, coeff)| g1 * coeff)
    .sum::<AffinePoint<PlutoExtendedCurve>>()
}

/// Open the commitment
pub fn open<const D: usize>(
  coeffs: Vec<PlutoScalarField>,
  eval_point: PlutoScalarField,
  g1_srs: Vec<AffinePoint<PlutoExtendedCurve>>,
) -> AffinePoint<PlutoExtendedCurve> {
  let poly = Polynomial::<Monomial, PlutoScalarField, D>::new(coeffs.try_into().unwrap_or_else(
    |v: Vec<PlutoScalarField>| panic!("Expected a Vec of length {} but it was {}", D, v.len()),
  ));
  let divisor =
    Polynomial::<Monomial, PlutoScalarField, 2>::new([-eval_point, PlutoScalarField::ONE]);

  let result = poly.div(divisor).coefficients;
  println!("resulting polynomial {:?}", result);

  commit(result.to_vec(), g1_srs)
}

/// Verify the polynomial evaluation.
pub fn check(
  p: AffinePoint<PlutoExtendedCurve>,
  q: AffinePoint<PlutoExtendedCurve>,
  point: PlutoScalarField,
  value: PlutoScalarField,
  g1_srs: Vec<AffinePoint<PlutoExtendedCurve>>,
  g2_srs: Vec<AffinePoint<PlutoExtendedCurve>>,
) -> bool {
  let g1 = *g1_srs.first().expect("has g1 srs");

  // This was the seeming bug, It now works for all polynomials, but am not sure why yet.
  let g2 = g2_srs[1];

  // e(pi, g2 - gen * point)
  let lhs =
    pairing::<PlutoExtendedCurve, 17>(q, g2 - AffinePoint::<PlutoExtendedCurve>::GENERATOR * point);

  // e(p - g1 * value, gen)
  let rhs =
    pairing::<PlutoExtendedCurve, 17>(p - g1 * value, AffinePoint::<PlutoExtendedCurve>::GENERATOR);
  println!("lhs {:?}", lhs);
  println!("rhs {:?}", rhs);

  lhs == rhs
}

// p = 101
// k = 2 (embedding degree, determines your extension field)
// base field = GF_101
// base scaler is 17 (number of points in the group)
// pairing output is in Extension field = GF_101^2?
// (all petals are in this base extension field: has two cyclic groups of order 17)

// Asymmetric  means G1 and G2 are different subgroups
// This is a little confusing teminology because all pairing friendly subgroups are isomorphic
// Symmetric means G1 and G2 are the same subgroup
