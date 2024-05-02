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
    // https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplicationcv
    let (x_p, y_p) = (p.x, p.y);
    let (x_q, y_q) = (q.x, q.y);

    // check for zero
    if x_p == x_q && y_p == -y_q {
      return Point { x: F::zero(), y: F::zero() };
    }

    // Check if point is itself, if it is you double (which is easier)
    let lamda = if x_p == x_q && y_p == y_q {
      (self.three * x_p * x_p + self.a) / (self.two * y_p)
    } else {
      (y_q - y_p) / (x_q - x_p)
    };

    let x = lamda * lamda - x_p - x_q;
    let y = lamda * (x_p - x) - y_p;
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