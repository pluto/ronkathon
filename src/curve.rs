use std::ops::Add;

use p3_field::{AbstractField, Field};

/// Elliptic curve in Weierstrass form: y^2 = x^3 + ax + b
pub struct Curve<F: Field> {
  pub a: F,
  pub b: F,
  three: F,
  two:   F,
}

pub struct CurvePoint<F: Field> {
  pub curve: Curve<F>,
  pub point: PointOrInfinity<F>,
}

#[derive(Clone, Copy)]
pub struct Point<F: Field> {
  x: F,
  y: F,
}

#[derive(Clone, Copy)]
pub enum PointOrInfinity<F: Field> {
  Point(Point<F>),
  Infinity,
}

impl<F: Field> Curve<F> {
  pub fn new(a: F, b: F) -> Self {
    Self {
      a,
      b,
      three: <F as AbstractField>::from_canonical_u8(3),
      two: <F as AbstractField>::from_canonical_u8(2),
    }
  }
}

impl<F: Field> CurvePoint<F> {
  pub fn new(curve: Curve<F>, x: F, y: F) -> Self {
    assert_eq!(y * y, x * x * x + curve.a * x + curve.b, "Point is not on curve");
    CurvePoint { curve, point: PointOrInfinity::Point(Point { x, y }) }
  }

  pub fn negate(&self, p: PointOrInfinity<F>) -> PointOrInfinity<F> {
    match p {
      PointOrInfinity::Point(p) => PointOrInfinity::Point(Point { x: p.x, y: -p.y }),
      PointOrInfinity::Infinity => PointOrInfinity::Infinity,
    }
  }

  fn add_points(&self, p: Point<F>, q: Point<F>) -> Point<F> {
    let (x1, y1) = (p.x, p.y);
    let (x2, y2) = (q.x, q.y);

    if x1 == x2 && y1 == -y2 {
      return Point { x: F::zero(), y: F::zero() };
    }

    let m = if x1 == x2 && y1 == y2 {
      (self.curve.three * x1 * x1 + self.curve.a) / (self.curve.two * y1)
    } else {
      (y2 - y1) / (x2 - x1)
    };

    let x = m * m - x1 - x2;
    let y = m * (x1 - x) - y1;

    Point { x, y }
  }
}

impl<F: Field> Add for CurvePoint<F> {
  type Output = CurvePoint<F>;

  fn add(self, other: CurvePoint<F>) -> CurvePoint<F> {
    match (self.point, other.point) {
      (PointOrInfinity::Infinity, _) => other,
      (_, PointOrInfinity::Infinity) => self,
      (PointOrInfinity::Point(p), PointOrInfinity::Point(q)) => {
        let r = self.add_points(p, q);
        CurvePoint { curve: self.curve, point: PointOrInfinity::Point(Point { x: r.x, y: r.y }) }
      },
    }
  }
}
