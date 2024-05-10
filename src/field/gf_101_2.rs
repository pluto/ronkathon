use super::*;

/// Pluto curve with modulus 101 supports two degree extension field. This can be verified
/// by finding out embedding degree of the curve, i.e. smallest k: r|q^k-1
const EXT_DEGREE: usize = 2;
const QUADRATIC_EXTENSION_FIELD_ORDER: u32 = 101 * 101;

#[derive(Clone, Default, Copy, Eq, PartialEq, Hash, Debug, Serialize, Deserialize)]

/// Quadratic Extension field element represented as polynomial of degree 1 in form:
/// a_0 + a_1*t where {a_0, a_1} \in \mathhbb{F}. Uses irreducible poly of the form:
/// (X^2-K).
pub struct Ext2<F: FiniteField> {
  pub(crate) value: [F; 2],
}

impl<F: FiniteField> Ext2<F> {
  const _D: usize = 2;

  pub const fn new(a: F, b: F) -> Self { Self { value: [a, b] } }

  /// irreducible polynomial used to reduce field polynomials to second degree:
  /// F[X]/(X^2-2)
  fn irreducible() -> F { -F::from_canonical_u32(2) }
}

impl<F: FiniteField> ExtensionField<F> for Ext2<F> {
  const D: usize = EXT_DEGREE;

  fn irreducible() -> F { Self::irreducible() }

  fn from_base(b: F) -> Self { Self { value: [b, F::ZERO] } }
}

impl<F: FiniteField> From<F> for Ext2<F> {
  fn from(value: F) -> Self { Self::from_base(value) }
}

impl<F: FiniteField> FiniteField for Ext2<F> {
  type Storage = u32;

  const NEG_ONE: Self = Self::new(F::NEG_ONE, F::ZERO);
  const ONE: Self = Self::new(F::ONE, F::ZERO);
  const ORDER: Self::Storage = QUADRATIC_EXTENSION_FIELD_ORDER;
  const THREE: Self = Self::new(F::THREE, F::ZERO);
  const TWO: Self = Self::new(F::TWO, F::ZERO);
  const ZERO: Self = Self::new(F::ZERO, F::ZERO);

  // field generator: can be verified using sage script
  // ```sage
  // F = GF(101)
  // Ft.<t> = F[]
  // P = Ft(t ^ 2 - 2)
  // F_2 = GF(101 ^ 2, name="t", modulus=P)
  // f_2_primitive_element = F_2([2, 1])
  // assert f_2_primitive_element.multiplicative_order() == 101^2-1
  // ```
  fn generator() -> Self { Self { value: [F::from_canonical_u32(14), F::from_canonical_u32(9)] } }

  /// Computes the multiplicative inverse of `a`, i.e. 1 / (a0 + a1 * t).
  /// Multiply by `a0 - a1 * t` in numerator and denominator.
  /// Denominator equals `(a0 + a1 * t) * (a0 - a1 * t) = a0.pow(2) - a1.pow(2) * Q::residue()`
  fn inverse(&self) -> Option<Self> {
    if *self == Self::ZERO {
      return None;
    }

    let mut res = Self::default();
    let scalar =
      (self.value[0].square() - Self::irreducible() * self.value[1].square()).inverse().unwrap();
    res.value[0] = self.value[0] * scalar;
    res.value[1] = -self.value[1] * scalar;
    Some(res)
  }

  fn primitive_root_of_unity(_n: Self::Storage) -> Self { todo!() }

  fn from_canonical_u32(n: u32) -> Self { Self { value: [F::from_canonical_u32(n), F::ZERO] } }
}

impl<F: FiniteField> Add for Ext2<F> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    let mut res = self.value;
    for (r, rhs_val) in res.iter_mut().zip(rhs.value) {
      *r += rhs_val;
    }

    Self { value: res }
  }
}

impl<F: FiniteField> AddAssign for Ext2<F> {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<F: FiniteField> Add<F> for Ext2<F> {
  type Output = Self;

  fn add(self, rhs: F) -> Self::Output {
    let mut res = self;
    res.value[0] += rhs;
    res
  }
}

impl<F: FiniteField> AddAssign<F> for Ext2<F> {
  fn add_assign(&mut self, rhs: F) { *self = *self + rhs; }
}

impl<F: FiniteField> Sub for Ext2<F> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let mut res = self.value;
    for (r, rhs_val) in res.iter_mut().zip(rhs.value) {
      *r -= rhs_val;
    }

    Self { value: res }
  }
}

impl<F: FiniteField> SubAssign for Ext2<F> {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<F: FiniteField> Sub<F> for Ext2<F> {
  type Output = Self;

  fn sub(self, rhs: F) -> Self::Output {
    let mut res = self;
    res.value[0] -= rhs;
    res
  }
}

impl<F: FiniteField> SubAssign<F> for Ext2<F> {
  fn sub_assign(&mut self, rhs: F) { *self = *self - rhs; }
}

impl<F: FiniteField> Sum for Ext2<F> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO)
  }
}

impl<F: FiniteField> Product for Ext2<F> {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl<F: FiniteField> Mul for Ext2<F> {
  type Output = Self;

  /// Returns the multiplication of `a` and `b` using the following equation:
  /// (a0 + a1 * t) * (b0 + b1 * t) = a0 * b0 + a1 * b1 * irreducible() + (a0 * b1 + a1 * b0) * t
  fn mul(self, rhs: Self) -> Self::Output {
    let a = self.value;
    let b = rhs.value;
    let mut res = Self::default();
    res.value[0] = a[0] * b[0] + a[1] * b[1] * Self::irreducible();
    res.value[1] = a[0] * b[1] + a[1] * b[0];
    res
  }
}

impl<F: FiniteField> MulAssign for Ext2<F> {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<F: FiniteField> Mul<F> for Ext2<F> {
  type Output = Self;

  fn mul(self, rhs: F) -> Self::Output {
    let mut res = self;
    res.value[0] *= rhs;
    res.value[1] *= rhs;
    res
  }
}

impl<F: FiniteField> MulAssign<F> for Ext2<F> {
  fn mul_assign(&mut self, rhs: F) { *self = *self * rhs; }
}

impl<F: FiniteField> Div for Ext2<F> {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().expect("invalid inverse") }
}

impl<F: FiniteField> DivAssign for Ext2<F> {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs }
}

impl<F: FiniteField> Neg for Ext2<F> {
  type Output = Self;

  fn neg(self) -> Self::Output { Self::ZERO - self }
}

impl<F: FiniteField> Rem for Ext2<F> {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
}

impl From<u32> for Ext2<GF101> {
  fn from(val: u32) -> Self { Self::new(GF101::from(val), GF101::ZERO) }
}

impl From<u64> for Ext2<GF101> {
  fn from(val: u64) -> Self { Self::new(GF101::from(val), GF101::ZERO) }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::curves::{g2_curve::G2Curve, AffinePoint};

  #[test]
  fn test_field() {
    let order = <Ext2<GF101>>::ORDER;
    assert_eq!(order, 101 * 101);

    let degree = <Ext2<GF101>>::D;
    assert_eq!(2, degree);
  }

  #[test]
  fn test_from_base() {
    let x = GF101::new(10);
    let x_2 = <Ext2<GF101>>::from_base(x);

    assert_eq!(x_2.value[0], GF101::new(10));
    assert_eq!(x_2.value[1], GF101::new(0));
  }

  #[test]
  fn test_add() {
    let a = <Ext2<GF101>>::new(GF101::new(10), GF101::new(20));
    let b = <Ext2<GF101>>::new(GF101::new(20), GF101::new(10));
    assert_eq!(a + b, <Ext2<GF101>>::new(GF101::new(30), GF101::new(30)));

    let c = <Ext2<GF101>>::new(GF101::new(70), GF101::new(80));
    let d = <Ext2<GF101>>::new(GF101::new(80), GF101::new(70));
    assert_eq!(c + d, <Ext2<GF101>>::new(GF101::new(49), GF101::new(49)));
  }

  #[test]
  fn test_sub() {
    let a = <Ext2<GF101>>::new(GF101::new(10), GF101::new(20));
    let b = <Ext2<GF101>>::new(GF101::new(20), GF101::new(10));
    assert_eq!(a - b, <Ext2<GF101>>::new(GF101::new(91), GF101::new(10)));
  }

  #[test]
  fn test_mul() {
    let a = <Ext2<GF101>>::new(GF101::new(10), GF101::new(20));
    let b = <Ext2<GF101>>::new(GF101::new(20), GF101::new(10));
    assert_eq!(a * b, <Ext2<GF101>>::new(GF101::new(2), GF101::new(96)));
  }

  #[test]
  fn test_add_sub_neg_mul() {
    let mut rng = rand::thread_rng();
    let x = <Ext2<GF101>>::from_base(rng.gen::<GF101>());
    let y = <Ext2<GF101>>::from_base(rng.gen::<GF101>());
    let z = <Ext2<GF101>>::from_base(rng.gen::<GF101>());
    assert_eq!(x + (-x), <Ext2<GF101>>::ZERO);
    assert_eq!(-x, <Ext2<GF101>>::ZERO - x);
    assert_eq!(x + x, x * <Ext2<GF101>>::TWO);
    assert_eq!(x * (-x), -(x * x));
    assert_eq!(x + y, y + x);
    assert_eq!(x * y, y * x);
    assert_eq!(x * (y * z), (x * y) * z);
    assert_eq!(x - (y + z), (x - y) - z);
    assert_eq!((x + y) - z, x + (y - z));
    assert_eq!(x * (y + z), x * y + x * z);
    assert_eq!(x + y + z + x + y + z, [x, x, y, y, z, z].iter().cloned().sum());
  }

  #[test]
  fn test_pow() {
    let mut rng = rand::thread_rng();
    let x = <Ext2<GF101>>::from_base(rng.gen::<GF101>());

    assert_eq!(x, x.pow(1));

    let res = x.pow(4);
    assert_eq!(res, x.square().square());
  }

  #[test]
  fn test_inv_div() {
    let mut rng = rand::thread_rng();
    // Loop rng's until we get something with inverse.
    let mut x = <Ext2<GF101>>::ZERO;
    let mut x_inv = None;
    while x_inv.is_none() {
      x = <Ext2<GF101>>::from_base(rng.gen::<GF101>());
      x_inv = x.inverse();
    }
    let mut y = <Ext2<GF101>>::ZERO;
    let mut y_inv = None;
    while y_inv.is_none() {
      y = <Ext2<GF101>>::from_base(rng.gen::<GF101>());
      y_inv = y.inverse();
    }
    let mut z = <Ext2<GF101>>::ZERO;
    let mut z_inv = None;
    while z_inv.is_none() {
      z = <Ext2<GF101>>::from_base(rng.gen::<GF101>());
      z_inv = z.inverse();
    }
    assert_eq!(x * x.inverse().unwrap(), <Ext2<GF101>>::ONE);
    assert_eq!(x.inverse().unwrap_or(<Ext2<GF101>>::ONE) * x, <Ext2<GF101>>::ONE);
    assert_eq!(
      x.square().inverse().unwrap_or(<Ext2<GF101>>::ONE),
      x.inverse().unwrap_or(<Ext2<GF101>>::ONE).square()
    );
    assert_eq!((x / y) * y, x);
    assert_eq!(x / (y * z), (x / y) / z);
    assert_eq!((x * y) / z, x * (y / z));
  }

  #[test]
  fn test_generator() {
    assert_eq!(
      <Ext2<GF101>>::generator() * GF101::from_canonical_u32(GF101::ORDER),
      <Ext2<GF101>>::ZERO
    );
  }

  #[test]
  fn test_add_sub_mul_subfield() {
    let mut rng = rand::thread_rng();
    let x = <Ext2<GF101>>::from_base(rng.gen::<GF101>());
    let y = rng.gen::<GF101>();

    let add1 = x + y;
    let sub1 = x - y;
    let res = x * GF101::TWO;
    assert_eq!(add1 + sub1, res);

    let mul1 = x * y;
    let inv_mul = x * y.inverse().unwrap();
    let res = x.square();
    assert_eq!(mul1 * inv_mul, res);
  }

  #[test]
  fn test_generator_order() {
    let generator = <Ext2<GF101>>::generator();

    let mut val = generator;
    for _ in 0..<Ext2<GF101>>::ORDER - 1 {
      val *= generator;
    }
    assert_eq!(val, generator);
  }

  #[test]
  fn test_point_doubling() {
    let g = AffinePoint::<G2Curve>::generator();

    let (x, y) = match g {
      AffinePoint::XY(x, y) => (x, y),
      AffinePoint::Infty => panic!("Cannot double point at infinity"),
    };

    // m = (3x^2) / (2y)
    let m = (<Ext2<GF101>>::THREE * x.square()) / (<Ext2<GF101>>::TWO * y);

    // 2P = (m^2 - 2x, m(3x - m^2) - y)
    let x_new = m.square() - <Ext2<GF101>>::TWO * x;
    let y_new = m * (<Ext2<GF101>>::THREE * x - m.square()) - y;

    let point_double: AffinePoint<G2Curve> = AffinePoint::new(x_new, y_new);

    // Check if the doubled point satisfies the curve equation
    assert_eq!(point_double, g.point_doubling());
  }
}
