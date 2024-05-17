//! Does the SRS setup for the KZG10 scheme.

use self::{curve::pairing::pairing, field::prime::PlutoScalarField};
use super::*;

/// simple setup to get params.
#[allow(dead_code, clippy::type_complexity)]
pub fn setup() -> (Vec<AffinePoint<PlutoExtendedCurve>>, Vec<AffinePoint<PlutoExtendedCurve>>) {
  // NOTE: For demonstration purposes only.

  // This is just tau from plonk by hand, it is not actually secure
  let tau: PlutoScalarField = PlutoScalarField::new(2);

  let g1 = AffinePoint::<PlutoExtendedCurve>::from(AffinePoint::<PlutoBaseCurve>::generator());
  let g2 = AffinePoint::<PlutoExtendedCurve>::generator();
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
  coefs: Vec<PlutoScalarField>,
  g1_srs: Vec<AffinePoint<PlutoExtendedCurve>>,
) -> AffinePoint<PlutoExtendedCurve> {
  assert!(g1_srs.len() >= coefs.len());

  g1_srs.into_iter().zip(coefs).map(|(g1, coef)| g1 * coef).sum::<AffinePoint<PlutoExtendedCurve>>()
}

/// Open the commitment
pub fn open(
  coefs: Vec<PlutoScalarField>,
  eval_point: PlutoScalarField,
  g1_srs: Vec<AffinePoint<PlutoExtendedCurve>>,
) -> AffinePoint<PlutoExtendedCurve> {
  let poly = Polynomial::<Monomial, PlutoScalarField>::new(coefs.clone());
  let divisor =
    Polynomial::<Monomial, PlutoScalarField>::new(vec![-eval_point, PlutoScalarField::ONE]);

  let result = poly.div(divisor).coefficients;
  println!("resulting polynomial {:?}", result);

  commit(result, g1_srs)
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
  // let p_gen =
  // AffinePoint::<PlutoExtendedCurve>::from(AffinePoint::<PlutoBaseCurve>::generator());
  // let cube_root_of_unity = PlutoBaseFieldExtension::primitive_root_of_unity(3);
  // let q_gen = if let AffinePoint::<PlutoBaseCurve>::Point(x, y) =
  //   AffinePoint::<PlutoBaseCurve>::generator()
  // {
  //   AffinePoint::<PlutoExtendedCurve>::new(
  //     cube_root_of_unity * PlutoBaseFieldExtension::from(x),
  //     PlutoBaseFieldExtension::from(y),
  //   )
  // } else {
  //   panic!("Generator is not a point");
  // };

  let g1 = *g1_srs.first().expect("has g1 srs");
  let g2 = *g2_srs.first().expect("has g2 srs");

  let lhs = pairing::<PlutoExtendedCurve, 17>(
    q.into(),
    g2 - AffinePoint::<PlutoExtendedCurve>::generator() * point,
  );

  let rhs = pairing::<PlutoExtendedCurve, 17>(
    (p - g1 * value).into(),
    AffinePoint::<PlutoExtendedCurve>::generator(),
  );
  println!("lhs {:?}", lhs);
  println!("rhs {:?}", rhs);

  lhs == rhs
}
