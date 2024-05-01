use p3_field::{AbstractField, Field};

/// Elliptic curve in Weierstrass form: y^2 = x^3 + ax + b
pub struct Curve<F: Field> {
  pub a: F,
  pub b: F,
  three: F,
  two:   F,
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

  pub fn negate(&self, p: PointOrInfinity<F>) -> PointOrInfinity<F> {
    match p {
      PointOrInfinity::Point(p) => PointOrInfinity::Point(Point { x: p.x, y: -p.y }),
      PointOrInfinity::Infinity => PointOrInfinity::Infinity,
    }
  }

  pub fn add(&self, p: PointOrInfinity<F>, q: PointOrInfinity<F>) -> PointOrInfinity<F> {
    match (p, q) {
      (PointOrInfinity::Infinity, _) => q,
      (_, PointOrInfinity::Infinity) => p,
      (PointOrInfinity::Point(p), PointOrInfinity::Point(q)) => {
        let r = self.add_points(p, q);
        PointOrInfinity::Point(Point { x: r.x, y: r.y })
      },
    }
  }

  fn add_points(&self, p: Point<F>, q: Point<F>) -> Point<F> {
    let (x1, y1) = (p.x, p.y);
    let (x2, y2) = (q.x, q.y);

    if x1 == x2 && y1 == -y2 {
      return Point { x: F::zero(), y: F::zero() };
    }

    let m = if x1 == x2 && y1 == y2 {
      (self.three * x1 * x1 + self.a) / (self.two * y1)
    } else {
      (y2 - y1) / (x2 - x1)
    };

    let x = m * m - x1 - x2;
    let y = m * (x1 - x) - y1;

    Point { x, y }
  }
}
