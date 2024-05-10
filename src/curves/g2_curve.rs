//! This module implements the G2 curve which is defined over the base field `GF101` and the
//! extension field `GF101^2`.

use super::*;

/// A container to implement curve parameters for the G2 curve.
/// The Elliptic curve $y^2=x^3+3$, i.e.
// a = 0
// b = 3
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct G2Curve;

impl EllipticCurve for G2Curve {
  type BaseField = Ext<2, GF101>;

  const EQUATION_A: Self::BaseField = Ext::<2, GF101>::ZERO;
  const EQUATION_B: Self::BaseField = Ext::<2, GF101>::new([GF101::new(3), GF101::ZERO]);
  const GENERATOR: (Self::BaseField, Self::BaseField) = (
    Ext::<2, GF101>::new([GF101::new(36), GF101::ZERO]),
    Ext::<2, GF101>::new([GF101::ZERO, GF101::new(31)]),
  );
  const ORDER: u32 = 289;
}

#[cfg(test)]
mod tests {
  use super::*;

  fn point() -> AffinePoint<G2Curve> {
    AffinePoint::<G2Curve>::new(
      Ext::<2, GF101>::new([GF101::new(90), GF101::ZERO]),
      Ext::<2, GF101>::new([GF101::ZERO, GF101::new(82)]),
    )
  }

  fn false_point() -> AffinePoint<G2Curve> {
    AffinePoint::<G2Curve>::new(
      Ext::<2, GF101>::new([GF101::new(36), GF101::ZERO]),
      Ext::<2, GF101>::new([GF101::ZERO, GF101::new(81)]),
    )
  }

  fn generator() -> AffinePoint<G2Curve> {
    AffinePoint::<G2Curve>::new(
      Ext::<2, GF101>::new([GF101::new(36), GF101::ZERO]),
      Ext::<2, GF101>::new([GF101::ZERO, GF101::new(31)]),
    )
  }

  #[rstest]
  #[case(AffinePoint::<G2Curve>::generator())]
  #[case(generator())]
  #[case(point())]
  #[should_panic]
  #[case(false_point())]
  fn on_curve(#[case] p: AffinePoint<G2Curve>) { let _ = p; }

  #[test]
  fn point_doubling() {
    let g = AffinePoint::<G2Curve>::generator();
    let two_g = g.point_doubling();

    let expected_g = generator();
    let expected_two_g = point();

    assert_eq!(two_g, expected_two_g);
    assert_eq!(g, expected_g);
  }

  #[test]
  fn scalar_multiplication_rhs() {
    let g = AffinePoint::<G2Curve>::generator();
    let two_g = g * 2;
    let expected_two_g = g.point_doubling();
    assert_eq!(two_g, expected_two_g);
    assert_eq!(-two_g, -expected_two_g);
  }

  #[test]
  fn scalar_multiplication_lhs() {
    let g = AffinePoint::<G2Curve>::generator();
    let two_g = 2 * g;
    let expected_two_g = g.point_doubling();
    assert_eq!(two_g, expected_two_g);
    assert_eq!(-two_g, -expected_two_g);
  }
}
