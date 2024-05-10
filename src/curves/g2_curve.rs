use std::ops::Add;

use super::CurveParams;
use crate::field::{gf_101::GF101, gf_101_2::QuadraticPlutoField, ExtensionField, FiniteField};

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct G2Curve {}
// The Elliptic curve $y^2=x^3+3$, i.e.
// a = 0
// b = 3

impl CurveParams for G2Curve {
  type FieldElement = QuadraticPlutoField<GF101>;

  const EQUATION_A: Self::FieldElement = QuadraticPlutoField::<GF101>::ZERO;
  const EQUATION_B: Self::FieldElement =
    QuadraticPlutoField::<GF101>::new(GF101::new(3), GF101::ZERO);
  const GENERATOR: (Self::FieldElement, Self::FieldElement) = (
    QuadraticPlutoField::<GF101>::new(GF101::new(36), GF101::ZERO),
    QuadraticPlutoField::<GF101>::new(GF101::ZERO, GF101::new(31)),
  );
  const ORDER: u32 = 289;
  // extension field subgroup should have order r^2 where r is order of first group
  const THREE: QuadraticPlutoField<GF101> =
    QuadraticPlutoField::<GF101>::new(GF101::new(3), GF101::ZERO);
  const TWO: QuadraticPlutoField<GF101> = QuadraticPlutoField::<GF101>::TWO;
}

mod test {
  use super::*;
  use crate::curves::AffinePoint;
  type F = QuadraticPlutoField<GF101>;

  #[test]
  fn point_doubling() {
    let g = AffinePoint::<G2Curve>::generator();
    let two_g = g.point_doubling();

    let expected_2g = AffinePoint::<G2Curve>::new(
      F::new(GF101::new(90), GF101::ZERO),
      F::new(GF101::ZERO, GF101::new(82)),
    );
    let expected_g = AffinePoint::<G2Curve>::new(
      F::new(GF101::new(36), GF101::ZERO),
      F::new(GF101::ZERO, GF101::new(31)),
    );

    assert_eq!(two_g, expected_2g);
    assert_eq!(g, expected_g);

    let four_g = two_g.point_doubling();
  }

  #[test]
  fn scalar_multiplication_rhs() {
    let g = AffinePoint::<G2Curve>::generator();
    let two_g = g * 2;
    let expected_2g = g.point_doubling();
    assert_eq!(two_g, expected_2g);
    assert_eq!(-two_g, -expected_2g);
  }

  #[test]
  fn scalar_multiplication_lhs() {
    let g = AffinePoint::<G2Curve>::generator();
    let two_g = 2 * g;
    let expected_2g = g.point_doubling();
    assert_eq!(two_g, expected_2g);
    assert_eq!(-two_g, -expected_2g);
  }
}
