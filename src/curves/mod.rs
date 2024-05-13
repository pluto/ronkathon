//! Elliptic curve operations and types.

use super::*;

pub mod pluto_curve;

/// Elliptic curve parameters for a curve over a finite field in Weierstrass form
/// `y^2 = x^3 + ax + b`
pub trait EllipticCurve: Copy {
  /// The field for the curve coefficients.
  type Coefficient: FiniteField + Into<Self::BaseField>;

  /// Integer field element type
  type BaseField: FiniteField;

  /// Order of this elliptic curve, i.e. number of elements in the scalar field.
  const ORDER: u32;

  /// Coefficient `a` in the Weierstrass equation of this elliptic curve.
  const EQUATION_A: Self::Coefficient;

  /// Coefficient `b` in the Weierstrass equation of this elliptic curve.
  const EQUATION_B: Self::Coefficient;

  /// Generator of this elliptic curve.
  const GENERATOR: (Self::BaseField, Self::BaseField);
}

// TODO: A potential issue here is that you can have a point that is not on the curve created via
// this enum. This is a potential issue that should be addressed.
/// An Affine Coordinate Point on a Weierstrass elliptic curve
#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub enum AffinePoint<C: EllipticCurve> {
  /// A point on the curve.
  PointOnCurve(C::BaseField, C::BaseField),

  /// The point at infinity.
  Infinity,
}

impl<C: EllipticCurve> AffinePoint<C> {
  /// Create a new point on the curve so long as it satisfies the curve equation.
  pub fn new(x: C::BaseField, y: C::BaseField) -> Self {
    assert_eq!(
      y * y,
      x * x * x + C::EQUATION_A.into() * x + C::EQUATION_B.into(),
      "Point is not on curve"
    );
    Self::PointOnCurve(x, y)
  }
}

// Example:
// Base

impl<C: EllipticCurve> Neg for AffinePoint<C> {
  type Output = AffinePoint<C>;

  fn neg(self) -> Self::Output {
    let (x, y) = match self {
      AffinePoint::PointOnCurve(x, y) => (x, -y),
      AffinePoint::Infinity => panic!("Cannot double point at infinity"),
    };
    AffinePoint::new(x, y)
  }
}

// TODO: This should likely use a `Self::ScalarField` instead of `u32`.
/// Scalar multiplication on the rhs: P*(u32)
/// This is the niave implementation of scalar multiplication
/// There is a faster way to do this but this is simpler to reason about for now
#[allow(clippy::suspicious_arithmetic_impl)]
impl<C: EllipticCurve> Mul<u32> for AffinePoint<C> {
  type Output = AffinePoint<C>;

  fn mul(mut self, scalar: u32) -> Self::Output {
    let val = self;
    for _ in 1..scalar {
      self = self + val;
    }
    self
  }
}

/// Scalar multiplication on the Lhs (u32)*P
impl<C: EllipticCurve> std::ops::Mul<AffinePoint<C>> for u32 {
  type Output = AffinePoint<C>;

  fn mul(self, _rhs: AffinePoint<C>) -> Self::Output {
    let mut result = AffinePoint::Infinity;
    let mut base = AffinePoint::generator();
    let mut exp = self;

    while exp > 0 {
      if exp % 2 == 1 {
        result = result + base;
      }
      base = base.point_doubling();
      exp /= 2;
    }
    result
  }
}

impl<C: EllipticCurve> Add for AffinePoint<C> {
  type Output = AffinePoint<C>;

  fn add(self, rhs: Self) -> Self::Output {
    // infty checks
    match (self, rhs) {
      (AffinePoint::Infinity, _) => return rhs,
      (_, AffinePoint::Infinity) => return self,

      _ => (),
    }
    let (x1, y1) = match self {
      AffinePoint::PointOnCurve(x, y) => (x, y),
      AffinePoint::Infinity => unreachable!(),
    };
    let (x2, y2) = match rhs {
      AffinePoint::PointOnCurve(x, y) => (x, y),
      AffinePoint::Infinity => unreachable!(),
    };
    if x1 == x2 && y1 == -y2 {
      return AffinePoint::Infinity;
    }
    // compute new point using elliptic curve point group law
    // https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication
    let lambda = if x1 == x2 && y1 == y2 {
      ((C::BaseField::TWO + C::BaseField::ONE) * x1 * x1 + C::EQUATION_A.into())
        / (C::BaseField::TWO * y1)
    } else {
      (y2 - y1) / (x2 - x1)
    };
    let x = lambda * lambda - x1 - x2;
    let y = lambda * (x1 - x) - y1;
    AffinePoint::new(x, y)
  }
}

// NOTE: Apparently there is a faster way to do this with twisted curve methods
impl<C: EllipticCurve> AffinePoint<C> {
  /// Compute the point doubling operation on this point.
  pub fn point_doubling(self) -> AffinePoint<C> {
    let (x, y) = match self {
      AffinePoint::PointOnCurve(x, y) => (x, y),
      AffinePoint::Infinity => panic!("Cannot double point at infinity"),
    };
    // m = (3x^2) + a / (2y) (a = 0 on our curve)
    let m = ((C::BaseField::TWO + C::BaseField::ONE) * x * x) / (C::BaseField::TWO * y);

    // 2P = (m^2 - 2x, m(3x - m^2)- y)
    let x_new = m * m - C::BaseField::TWO * x;
    let y_new = m * ((C::BaseField::TWO + C::BaseField::ONE) * x - m * m) - y;
    AffinePoint::new(x_new, y_new)
  }

  /// Get the generator point of this curve.
  pub fn generator() -> Self {
    let (x, y) = C::GENERATOR;
    AffinePoint::new(x, y)
  }
}
