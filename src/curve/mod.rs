//! Elliptic curve operations and types.
#![doc = include_str!("./README.md")]
use std::fmt::Debug;

use algebra::{
  field::FiniteField,
  group::{AbelianGroup, FiniteGroup},
  Finite,
};

use super::*;
use crate::{
  algebra::group::{FiniteCyclicGroup, Group},
  Field, PlutoScalarField,
};

pub mod pairing;
pub mod pluto_curve;
#[cfg(test)] mod tests;

/// Elliptic curve parameters for a curve over a finite field in Weierstrass form
/// `y^2 = x^3 + ax + b`
pub trait EllipticCurve: Copy + Debug + Eq {
  /// The field for the curve coefficients.
  type Coefficient: Field + Into<Self::BaseField>;

  /// curve base field element type
  /// TODO: need to be converted for big integers later
  type BaseField: FiniteField + Into<usize>;

  /// Curve scalar field type
  type ScalarField: FiniteField + Into<usize>;

  /// Order of this elliptic curve, i.e. number of elements in the scalar field.
  const ORDER: usize;

  /// Coefficient `a` in the Weierstrass equation of this elliptic curve.
  const EQUATION_A: Self::Coefficient;

  /// Coefficient `b` in the Weierstrass equation of this elliptic curve.
  const EQUATION_B: Self::Coefficient;

  /// Generator of the scalar field to the elliptic curve.
  const GENERATOR: (Self::BaseField, Self::BaseField);
}

/// Curve group representing curve element
pub trait CurveGroup: FiniteCyclicGroup {
  /// Curve group's base field
  type BaseField: Field + Into<usize>;

  /// Point doubling
  fn double(self) -> Self;
  /// Checks whether a point is on curve
  fn is_on_curve(&self) -> bool;

  /// Returns affine point `(x, y)`, returns `(_, _, true)` if point is `infinity`
  fn xy(&self) -> (Self::BaseField, Self::BaseField, bool);
}

// TODO: A potential issue here is that you can have a point that is not on the curve created via
// this enum. This is a potential issue that should be addressed.
/// An Affine Coordinate Point on a Weierstrass elliptic curve
#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub enum AffinePoint<C: EllipticCurve> {
  /// A point on the curve.
  Point(C::BaseField, C::BaseField),

  /// The point at infinity.
  Infinity,
}

impl<C: EllipticCurve> AffinePoint<C> {
  /// Create a new point on the curve so long as it satisfies the curve equation.
  pub fn new(x: C::BaseField, y: C::BaseField) -> Self {
    let point = Self::Point(x, y);
    assert!(point.is_on_curve(), "Point is not on curve");
    point
  }
}

impl<C: EllipticCurve> Finite for AffinePoint<C> {
  const ORDER: usize = C::ORDER;
}

impl<C: EllipticCurve> Group for AffinePoint<C> {
  type Scalar = C::ScalarField;

  const IDENTITY: Self = AffinePoint::Infinity;

  fn op(&self, b: &Self) -> Self { self.add(*b) }

  fn inverse(&self) -> Option<Self> {
    let (x, y) = match self {
      AffinePoint::Infinity => return Some(*self),
      AffinePoint::Point(x, y) => (*x, *y),
    };
    Some(AffinePoint::Point(-x, y))
  }

  fn scalar_mul(&self, b: Self::Scalar) -> Self { *self * b }
}

impl<C: EllipticCurve> FiniteGroup for AffinePoint<C> {}
impl<C: EllipticCurve> AbelianGroup for AffinePoint<C> {}

impl<C: EllipticCurve> CurveGroup for AffinePoint<C> {
  type BaseField = C::BaseField;

  // NOTE: Apparently there is a faster way to do this with twisted curve methods
  fn double(self) -> Self {
    let (x, y) = match self {
      AffinePoint::Point(x, y) => (x, y),
      AffinePoint::Infinity => return AffinePoint::Infinity,
    };
    // m = (3x^2) / (2y)
    let m = (((C::BaseField::ONE + C::BaseField::ONE) + C::BaseField::ONE) * x * x
      + C::EQUATION_A.into())
      / ((C::BaseField::ONE + C::BaseField::ONE) * y);

    // 2P = (m^2 - 2x, m(3x - m^2)- y)
    let x_new = m * m - (C::BaseField::ONE + C::BaseField::ONE) * x;
    let y_new = m * ((C::BaseField::ONE + C::BaseField::ONE + C::BaseField::ONE) * x - m * m) - y;
    AffinePoint::new(x_new, y_new)
  }

  fn is_on_curve(&self) -> bool {
    match self {
      AffinePoint::Infinity => true,
      AffinePoint::Point(x, y) => {
        let a: C::BaseField = C::EQUATION_A.into();
        let b: C::BaseField = C::EQUATION_B.into();
        *y * *y == *x * *x * *x + a * *x + b
      },
    }
  }

  fn xy(&self) -> (Self::BaseField, Self::BaseField, bool) {
    match self {
      AffinePoint::Infinity => (Self::BaseField::ZERO, Self::BaseField::ZERO, true),
      AffinePoint::Point(x, y) => (*x, *y, false),
    }
  }
}

impl<C: EllipticCurve> FiniteCyclicGroup for AffinePoint<C> {
  const GENERATOR: Self = AffinePoint::Point(C::GENERATOR.0, C::GENERATOR.1);
}

impl<C: EllipticCurve> Default for AffinePoint<C> {
  fn default() -> Self { <Self as FiniteCyclicGroup>::GENERATOR }
}

impl<C: EllipticCurve> Mul<C::ScalarField> for AffinePoint<C> {
  type Output = Self;

  /// This is the naive implementation of scalar multiplication
  /// There is a faster way to do this but this is simpler to reason about for now
  fn mul(self, rhs: C::ScalarField) -> Self::Output {
    if rhs == C::ScalarField::ZERO {
      return AffinePoint::Infinity;
    }
    let mut val = self;
    for _ in 1..rhs.into() {
      val += self;
    }
    val
  }
}

impl<C: EllipticCurve> MulAssign<C::ScalarField> for AffinePoint<C> {
  fn mul_assign(&mut self, rhs: C::ScalarField) { *self = *self * rhs }
}

impl<C: EllipticCurve> Add for AffinePoint<C> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    // infty checks
    match (self, rhs) {
      (AffinePoint::Infinity, _) => return rhs,
      (_, AffinePoint::Infinity) => return self,

      _ => (),
    }
    let (x1, y1) = match self {
      AffinePoint::Point(x, y) => (x, y),
      AffinePoint::Infinity => unreachable!(),
    };
    let (x2, y2) = match rhs {
      AffinePoint::Point(x, y) => (x, y),
      AffinePoint::Infinity => unreachable!(),
    };
    if x1 == x2 && y1 == -y2 {
      return AffinePoint::Infinity;
    }
    // compute new point using elliptic curve point group law
    // https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication
    let lambda = if x1 == x2 && y1 == y2 {
      ((C::BaseField::ONE + C::BaseField::ONE + C::BaseField::ONE) * x1 * x1 + C::EQUATION_A.into())
        / ((C::BaseField::ONE + C::BaseField::ONE) * y1)
    } else {
      (y2 - y1) / (x2 - x1)
    };
    let x = lambda * lambda - x1 - x2;
    let y = lambda * (x1 - x) - y1;

    AffinePoint::new(x, y)
  }
}

impl<C: EllipticCurve> AddAssign for AffinePoint<C> {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<C: EllipticCurve> Sum for AffinePoint<C> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(AffinePoint::Infinity)
  }
}

impl<C: EllipticCurve> Neg for AffinePoint<C> {
  type Output = AffinePoint<C>;

  fn neg(self) -> Self::Output {
    let (x, y) = match self {
      AffinePoint::Point(x, y) => (x, -y),
      AffinePoint::Infinity => return AffinePoint::Infinity,
    };
    AffinePoint::new(x, y)
  }
}

#[allow(clippy::suspicious_arithmetic_impl)]

impl<C: EllipticCurve> Sub for AffinePoint<C> {
  type Output = AffinePoint<C>;

  fn sub(self, rhs: Self) -> Self::Output { self + -rhs }
}

impl<C: EllipticCurve> SubAssign for AffinePoint<C> {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<C: EllipticCurve> std::ops::Mul<AffinePoint<C>> for u32 {
  type Output = AffinePoint<C>;

  fn mul(self, val: AffinePoint<C>) -> Self::Output {
    if self == 0 {
      return AffinePoint::Infinity;
    }
    let mut out = val;
    for _ in 1..self {
      out += val;
    }
    out
  }
}
