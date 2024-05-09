use super::*;

/// Elliptic curve in Weierstrass form: y^2 = x^3 + ax + b
pub struct Curve<F: FiniteField> {
  pub a:  F,
  pub b:  F,
  _three: F,
  _two:   F,
}
/// Example:
/// say 2 is in GF101
pub trait CurveParams: 'static + Copy + Clone + fmt::Debug + Default + Eq + Ord {
  /// Integer field element type
  type FieldElement: FiniteField + Neg;
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

/// An Affine Coordinate Point on a Weierstrass elliptic curve
#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub enum AffinePoint<C: CurveParams> {
  XY(C::FieldElement, C::FieldElement),
  Infty,
}

impl<C: CurveParams> AffinePoint<C> {
  pub fn new(x: C::FieldElement, y: C::FieldElement) -> Self {
    println!("X: {:?}, Y: {:?}", x, y);
    // okay so this is breaking because the curve equation doesn't know how to plug in polynomials.
    // y = 31x -> y^2 = 52x^2
    // x = 36 -> x^3 = 95 + 3
    // 52x^2 = 98 ???
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

// Example:
// Base

impl<C: CurveParams> std::ops::Neg for AffinePoint<C> {
  type Output = AffinePoint<C>;

  fn neg(self) -> Self::Output {
    let (x, y) = match self {
      AffinePoint::XY(x, y) => (x, y),
      AffinePoint::Infty => panic!("Cannot double point at infinity"),
    };
    AffinePoint::new(x, C::FieldElement::ZERO - y)
  }
}
/// Scalar multiplication on the rhs: P*(u32)
impl<C: CurveParams> std::ops::Mul<u32> for AffinePoint<C> {
  type Output = AffinePoint<C>;

  fn mul(self, scalar: u32) -> Self::Output {
    let mut result = AffinePoint::new_infty();
    let mut base = self;
    let mut exp = scalar;

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

/// Scalar multiplication on the Lhs (u32)*P
impl<C: CurveParams> std::ops::Mul<AffinePoint<C>> for u32 {
  type Output = AffinePoint<C>;

  fn mul(self, _rhs: AffinePoint<C>) -> Self::Output {
    let mut result = AffinePoint::new_infty();
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

impl<C: CurveParams> AffinePoint<C> {
  pub fn point_doubling(self) -> AffinePoint<C> {
    let (x, y) = match self {
      AffinePoint::XY(x, y) => (x, y),
      AffinePoint::Infty => panic!("Cannot double point at infinity"),
    };
    // m = 3x^2 / 26
    let m = (C::THREE * x * x) / (C::TWO * y);

    // 2P = (m^2 - 2x, m(3x - m^2)- y)
    let x_new = m * m - C::TWO * x;
    let y_new = m * (C::THREE * x - m * m) - y;
    AffinePoint::new(x_new, y_new)
  }

  pub fn generator() -> Self {
    let (x, y) = C::GENERATOR;
    println!("X: {:?}, Y: {:?}", x, y);
    AffinePoint::new(x, y)
  }
}

pub mod g1_curve;
pub mod g2_curve;
