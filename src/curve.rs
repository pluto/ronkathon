use std::{
  fmt,
  ops::{Add, Neg},
};

use crate::field::{gf_101::GF101, FiniteField};

/// Elliptic curve in Weierstrass form: y^2 = x^3 + ax + b
pub struct Curve<F: FiniteField> {
  pub a: F,
  pub b: F,
  three: F,
  two:   F,
}

pub trait CurveParams: 'static + Copy + Clone + fmt::Debug + Default + Eq + Ord {
  /// Integer field element type
  type FieldElement: FiniteField;
  /// Order of this elliptic curve, i.e. number of elements in the scalar field.
  const ORDER: u32;
  /// Coefficient `a` in the Weierstrass equation of this elliptic curve.
  const EQUATION_A: Self::FieldElement;
  /// Coefficient `b` in the Weierstrass equation of this elliptic curve.
  const EQUATION_B: Self::FieldElement;
  /// Generator of this elliptic curve.
  const GENERATOR: (Self::FieldElement, Self::FieldElement);
  // hack: 3 and 2 to satisfy the Add<AffinePoint> trait implementation
  const THREE: Self::FieldElement;
  const TWO: Self::FieldElement;

  // maybe Curve::uint type is diff from PCP::fieldelement type
  // maybe:
  // type AffinePoint;
  // type ProjectivePoint;
  // type Scalar;
}

/// The Elliptic curve $y^2=x^3+3$, i.e.
/// - a = 0
/// - b = 3
/// - generator todo
/// - order todo
/// - field element type todo, but mock with u64 - bad thor, u64 does not implement p3_field
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct C101;

impl CurveParams for C101 {
  type FieldElement = GF101;

  const EQUATION_A: Self::FieldElement = GF101::new(0);
  const EQUATION_B: Self::FieldElement = GF101::new(3);
  const GENERATOR: (Self::FieldElement, Self::FieldElement) = todo!();
  const ORDER: u32 = GF101::ORDER;
  const THREE: Self::FieldElement = GF101::new(3);
  const TWO: Self::FieldElement = GF101::new(2);
}

/// An Affine Coordinate Point on a Weierstrass elliptic curve
#[derive(Clone, Debug, Copy)]
pub enum AffinePoint<C: CurveParams> {
  XY(C::FieldElement, C::FieldElement),
  Infty,
}

impl<C: CurveParams> AffinePoint<C> {
  pub fn new(x: C::FieldElement, y: C::FieldElement) -> Self {
    assert_eq!(y * y, x * x * x + C::EQUATION_A * x + C::EQUATION_B, "Point is not on curve");
    Self::XY(x, y)
  }

  pub fn new_infty() -> Self { Self::Infty }

  pub fn negate(&mut self) {
    match self {
      Self::XY(_x, ref mut y) => *y = -*y,
      Self::Infty => (),
    }
  }
}

impl<C: CurveParams> Add for AffinePoint<C> {
  type Output = AffinePoint<C>;

  fn add(self, rhs: Self) -> Self::Output {
    // infty checks
    match (self, rhs) {
      (AffinePoint::Infty, _) => return rhs,
      (_, AffinePoint::Infty) => return self,

      _ => (),
    }
    let (x1, y1) = match self {
      AffinePoint::XY(x, y) => (x, y),
      AffinePoint::Infty => unreachable!(),
    };
    let (x2, y2) = match rhs {
      AffinePoint::XY(x, y) => (x, y),
      AffinePoint::Infty => unreachable!(),
    };
    if x1 == x2 && y1 == -y2 {
      return AffinePoint::new_infty();
    }
    // compute new point using elliptic curve point group law
    // https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication
    let lambda = if x1 == x2 && y1 == y2 {
      (C::THREE * x1 * x1 + C::EQUATION_A) / (C::TWO * y1)
    } else {
      (y2 - y1) / (x2 - x1)
    };
    let x = lambda * lambda - x1 - x2;
    let y = lambda * (x1 - x) - y1;
    AffinePoint::new(x, y)
  }
}
