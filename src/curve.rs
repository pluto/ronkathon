use std::{fmt, ops::Add};

use p3_field::{AbstractField, Field};

use crate::field::PlutoField;

/// Elliptic curve in Weierstrass form: y^2 = x^3 + ax + b
pub struct Curve<F: Field> {
  pub a: F,
  pub b: F,
  three: F,
  two:   F,
}

pub trait CurveParams: 'static + Copy + Clone + fmt::Debug + Default + Eq + Ord {
  /// Integer field element type
  type FieldElement: Field;
  /// Order of this elliptic curve, i.e. number of elements in the scalar field.
  const ORDER: u32;
  /// Coefficient `a` in the Weierstrass equation of this elliptic curve.
  const EQUATION_A: Self::FieldElement;
  /// Coefficient `b` in the Weierstrass equation of this elliptic curve.
  const EQUATION_B: Self::FieldElement;
  /// Generator of this elliptic curve.
  const GENERATOR: (Self::FieldElement, Self::FieldElement);

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
/// (~colin: bullish)
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct C101;

impl CurveParams for C101 {
  type FieldElement = crate::field::PlutoField;

  const EQUATION_A: Self::FieldElement = PlutoField::const_new(0);
  const EQUATION_B: Self::FieldElement = PlutoField::const_new(3);
  const GENERATOR: (Self::FieldElement, Self::FieldElement) = todo!();
  const ORDER: u32 = PlutoField::ORDER_U32;
}

/// An Affine Coordinate Point on a Weierstrass elliptic curve
#[derive(Clone, Debug, Copy)]
pub struct AffinePoint<C: CurveParams> {
  x:     C::FieldElement,
  y:     C::FieldElement,
  /// is the point the point at infinity
  infty: bool,
}

// impl<F: Field> Curve<F> {
//   pub fn new(a: F, b: F) -> Self {
//     Self {
//       a,
//       b,
//       three: <F as AbstractField>::from_canonical_u8(3),
//       two: <F as AbstractField>::from_canonical_u8(2),
//     }
//   }
// }

// impl<F: Field> CurvePoint<F> {
//   pub fn new(curve: Curve<F>, x: F, y: F) -> Self {
//     assert_eq!(y * y, x * x * x + curve.a * x + curve.b, "Point is not on curve");
//     CurvePoint { curve, point: PointOrInfinity::Point(Point { x, y }) }
//   }

//   pub fn negate(&self, p: PointOrInfinity<F>) -> PointOrInfinity<F> {
//     match p {
//       PointOrInfinity::Point(p) => PointOrInfinity::Point(Point { x: p.x, y: -p.y }),
//       PointOrInfinity::Infinity => PointOrInfinity::Infinity,
//     }
//   }

//   fn add_points(&self, p: Point<F>, q: Point<F>) -> Point<F> {
//     // https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplicationcv
//     let (x_p, y_p) = (p.x, p.y);
//     let (x_q, y_q) = (q.x, q.y);

//     // check for zero
//     if x_p == x_q && y_p == -y_q {
//       return Point { x: F::zero(), y: F::zero() };
//     }

//     // Check if point is itself, if it is you double (which is easier)
//     let lamda = if x_p == x_q && y_p == y_q {
//       (self.curve.three * x_p * x_p + self.curve.a) / (self.curve.two * y_p)
//     } else {
//       (y_q - y_p) / (x_q - x_p)
//     };

//     let x = lamda * lamda - x_p - x_q;
//     let y = lamda * (x_p - x) - y_p;
//     Point { x, y }
//   }
// }

// impl<F: Field> Add for CurvePoint<F> {
//   type Output = CurvePoint<F>;

//   fn add(self, other: CurvePoint<F>) -> CurvePoint<F> {
//     match (self.point, other.point) {
//       (PointOrInfinity::Infinity, _) => other,
//       (_, PointOrInfinity::Infinity) => self,
//       (PointOrInfinity::Point(p), PointOrInfinity::Point(q)) => {
//         let r = self.add_points(p, q);
//         CurvePoint { curve: self.curve, point: PointOrInfinity::Point(Point { x: r.x, y: r.y }) }
//       },
//     }
//   }
// }
