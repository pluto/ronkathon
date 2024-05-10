//! This module implements the G2 curve which is defined over the base field `GF101` and the
//! extension field `GF101^2`.

use super::*;

// TODO: This seems unecessary?
/// A container to implement curve parameters for the G2 curve.
/// The Elliptic curve $y^2=x^3+3$, i.e.
// a = 0
// b = 3
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct G2Curve;

impl CurveParams for G2Curve {
  type BaseField = Ext<2, GF101>;

  const EQUATION_A: Self::BaseField = Ext::<2, GF101>::ZERO;
  const EQUATION_B: Self::BaseField = Ext::<2, GF101>::new([GF101::new(3), GF101::ZERO]);
  const GENERATOR: (Self::BaseField, Self::BaseField) = (
    Ext::<2, GF101>::new([GF101::new(36), GF101::ZERO]),
    Ext::<2, GF101>::new([GF101::ZERO, GF101::new(31)]),
  );
  const ORDER: u32 = 289;
}

// a naive impl with affine point

impl G2Curve {
  /// Create a new point on the curve so long as it satisfies the curve equation.
  pub fn on_curve(x: Ext<2, GF101>, y: Ext<2, GF101>) -> (Ext<2, GF101>, Ext<2, GF101>) {
    println!("X: {:?}, Y: {:?}", x, y);
    // TODO Continue working on this
    //                  (   x  )  (  y   )  ( x , y )
    // example: plug in ((36, 0), (0, 31)): (36, 31t)
    // x = 36, y = 31t,
    // curve : y^2=x^3+3,

    // y = (31t)^2 = 52 * t^2
    // check if there are any x terms, if not, element is in base field
    let mut lhs = x;
    let mut rhs = y;
    if lhs.coeffs[1] != GF101::ZERO {
      lhs = x * x * (-GF101::new(2)) - Self::EQUATION_B;
    } else {
      lhs = x * x * x - Self::EQUATION_B;
    }
    if y.coeffs[1] != GF101::ZERO {
      // y has degree two so if there is a x -> there will be an x^2 term which we substitude with
      // -2 since... TODO explain this and relationship to embedding degree
      rhs *= -GF101::new(2);
    }
    // minus
    lhs -= Self::EQUATION_B;
    assert_eq!(lhs, rhs, "Point is not on curve");
    (x, y)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn point_doubling() {
    let g = AffinePoint::<G2Curve>::generator();
    let two_g = g.point_doubling();

    let expected_2g = AffinePoint::<G2Curve>::new(
      Ext::<2, GF101>::new([GF101::new(90), GF101::ZERO]),
      Ext::<2, GF101>::new([GF101::ZERO, GF101::new(82)]),
    );
    let expected_g = AffinePoint::<G2Curve>::new(
      Ext::<2, GF101>::new([GF101::new(36), GF101::ZERO]),
      Ext::<2, GF101>::new([GF101::ZERO, GF101::new(31)]),
    );

    assert_eq!(two_g, expected_2g);
    assert_eq!(g, expected_g);
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
