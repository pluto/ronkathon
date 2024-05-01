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

// Since EVERY point is either at "infinity" or not, the coproduct makes sense. 
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

  // inverse
  pub fn negate(&self, p: PointOrInfinity<F>) -> PointOrInfinity<F> {
    match p {
      PointOrInfinity::Point(p) => PointOrInfinity::Point(Point { x: p.x, y: -p.y }),
      PointOrInfinity::Infinity => PointOrInfinity::Infinity,
    }
  }

  // outer add does infinitity check
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
