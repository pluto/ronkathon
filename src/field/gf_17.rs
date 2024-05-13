//! Implementation of the GF(17) field.

use super::*;

/// The prime number that defines order for the scalar field of the elliptic curve used in this
/// crate.
pub const ORDER: u32 = 17;

/// [`GF17`] represents the finite field GF(17) that has 17 elements and works with typical sum
/// and multiplication operations modulo 17.
#[derive(Copy, Clone, Default, Debug, Hash, PartialEq, Eq)]
pub struct GF17 {
  value: u32,
}

impl std::fmt::Display for GF17 {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}", self.value) }
}

impl GF17 {
  /// Create a new [`GF101`] element from the given value. The value is reduced modulo 101 to
  /// ensure it is within the field.
  pub const fn new(value: u32) -> Self { Self { value: value % ORDER } }
}

impl FiniteField for GF17 {
  type Storage = u32;

  const NEG_ONE: Self = Self::new(Self::ORDER - 1);
  const ONE: Self = Self::new(1);
  const ORDER: Self::Storage = ORDER;
  const THREE: Self = Self::new(3);
  const TWO: Self = Self::new(2);
  const ZERO: Self = Self::new(0);

  fn inverse(&self) -> Option<Self> {
    if self.value == 0 {
      return None;
    }
    let exponent = Self::ORDER - 2;
    let mut result = Self::ONE;
    let mut base = *self;
    let mut power = exponent;

    while power > 0 {
      if power & 1 == 1 {
        result *= base;
      }
      base = base * base;
      power >>= 1;
    }
    Some(result)
  }

  fn generator() -> Self { Self::new(2) }
}

impl Add for GF17 {
  type Output = Self;

  fn add(self, rhs: Self) -> Self { Self { value: (self.value + rhs.value) % Self::ORDER } }
}

impl AddAssign for GF17 {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl Sum for GF17 {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO)
  }
}

impl Sub for GF17 {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let (mut diff, over) = self.value.overflowing_sub(rhs.value);
    let corr = if over { Self::ORDER } else { 0 };
    diff = diff.wrapping_add(corr);
    Self { value: diff }
  }
}

impl SubAssign for GF17 {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl Mul for GF17 {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self { Self { value: (self.value * rhs.value) % Self::ORDER } }
}

impl MulAssign for GF17 {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl Product for GF17 {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl Div for GF17 {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self { self * rhs.inverse().unwrap() }
}

impl DivAssign for GF17 {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl Neg for GF17 {
  type Output = Self;

  fn neg(self) -> Self::Output { Self::ZERO - self }
}

impl Rem for GF17 {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self { self - (self / rhs) * rhs }
}

impl Distribution<GF17> for Standard {
  #[inline]
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> GF17 {
    loop {
      let next_u31 = rng.next_u32() >> 4;
      let is_canonical = next_u31 < GF17::ORDER;
      if is_canonical {
        return GF17 { value: next_u31 };
      }
    }
  }
}

impl From<u32> for GF17 {
  fn from(val: u32) -> Self { Self::new(val) }
}

impl From<u64> for GF17 {
  fn from(val: u64) -> Self { Self::new(val as u32) }
}

impl From<usize> for GF17 {
  fn from(val: usize) -> Self { Self::new(val as u32) }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[rstest]
  #[case(GF17::new(0), GF17::new(0), GF17::new(0))]
  #[case(GF17::new(1), GF17::new(1), GF17::new(2))]
  #[case(GF17::new(12), GF17::new(5), GF17::new(0))]
  #[case(GF17::new(5), GF17::new(12), GF17::new(0))]
  #[case(GF17::new(10), GF17::new(10), GF17::new(3))]
  fn add(#[case] a: GF17, #[case] b: GF17, #[case] expected: GF17) {
    assert_eq!(a + b, expected);
  }

  #[rstest]
  #[case(GF17::new(0), GF17::new(0), GF17::new(0))]
  #[case(GF17::new(1), GF17::new(1), GF17::new(0))]
  #[case(GF17::new(12), GF17::new(5), GF17::new(7))]
  #[case(GF17::new(5), GF17::new(12), GF17::new(10))]
  #[case(GF17::new(10), GF17::new(10), GF17::new(0))]
  fn sub(#[case] a: GF17, #[case] b: GF17, #[case] expected: GF17) {
    assert_eq!(a - b, expected);
  }

  #[rstest]
  #[case(GF17::new(0), GF17::new(0))]
  #[case(GF17::new(10), GF17::new(5))]
  #[case(GF17::new(12), GF17::new(6))]
  #[case(GF17::new(1), GF17::new(9))]
  #[case(GF17::new(3), GF17::new(10))]
  fn halve(#[case] a: GF17, #[case] expected: GF17) {
    assert_eq!(a / GF17::TWO, expected);
  }

  #[rstest]
  #[case(GF17::new(0), GF17::new(0), GF17::new(0))]
  #[case(GF17::new(1), GF17::new(1), GF17::new(1))]
  #[case(GF17::new(12), GF17::new(5), GF17::new(9))]
  #[case(GF17::new(5), GF17::new(12), GF17::new(9))]
  #[case(GF17::new(10), GF17::new(10), GF17::new(15))]
  fn mul(#[case] a: GF17, #[case] b: GF17, #[case] expected: GF17) {
    assert_eq!(a * b, expected);
  }

  #[test]
  fn zero() {
    let f = GF17::new(0);
    assert_eq!(f.value, 0);

    let f = GF17::new(GF17::ORDER);
    assert_eq!(f.value, 0);
  }

  #[rstest]
  #[case(GF17::new(0), 0, GF17::new(1))]
  #[case(GF17::new(0), 10, GF17::new(0))]
  #[case(GF17::new(12), 5, GF17::new(3))]
  #[case(GF17::new(5), 12, GF17::new(4))]
  #[case(GF17::new(10), 10, GF17::new(2))]
  fn exp_generic(#[case] a: GF17, #[case] pow: u64, #[case] expected: GF17) {
    assert_eq!(a.pow(pow), expected);
  }

  #[test]
  fn add_sub_neg_mul() {
    let mut rng = rand::thread_rng();
    // for i in 0..1000 {
    let x = rng.gen::<GF17>();
    let y = rng.gen::<GF17>();
    let z = rng.gen::<GF17>();
    assert_eq!(x + (-x), GF17::ZERO);
    assert_eq!(-x, GF17::ZERO - x);
    assert_eq!(x + x, x * GF17::TWO);
    assert_eq!(x, x.div(GF17::new(2)) * GF17::TWO);
    assert_eq!(x * (-x), -(x * x));
    assert_eq!(x + y, y + x);
    assert_eq!(x * y, y * x);
    assert_eq!(x * (y * z), (x * y) * z);
    assert_eq!(x - (y + z), (x - y) - z);
    assert_eq!((x + y) - z, x + (y - z));
    assert_eq!(x * (y + z), x * y + x * z);
    assert_eq!(x + y + z + x + y + z, [x, x, y, y, z, z].iter().cloned().sum());
  }

  #[rstest]
  #[should_panic]
  // First case will panic here so the "expected" value is not relevant.
  #[case(GF17::new(0), GF17::new(69420))]
  #[case(GF17::new(1), GF17::new(1))]
  #[case(GF17::new(12), GF17::new(10))]
  #[case(GF17::new(5), GF17::new(7))]
  #[case(GF17::new(10), GF17::new(12))]
  fn multiplicative_inverse(#[case] a: GF17, #[case] expected: GF17) {
    assert_eq!(a.inverse().unwrap(), expected);
    assert_eq!(a.inverse().unwrap() * a, GF17::ONE);
  }

  #[test]
  fn identity_elements() {
    let zero = GF17::new(0);
    let one = GF17::new(1);
    for i in 0..GF17::ORDER {
      let f = GF17::new(i);
      assert_eq!(f + zero, f);
      assert_eq!(f * one, f);
      assert_eq!(f * zero, zero);
    }
  }

  #[test]
  fn negation() {
    for i in 0..GF17::ORDER {
      let a = GF17::new(i);
      let neg_a = -a;
      assert_eq!(a + neg_a, GF17::ZERO);
    }
  }

  #[test]
  fn inverse_of_inverse() {
    for i in 1..GF17::ORDER {
      let a = GF17::new(i);
      let a_inv = a.inverse().unwrap();
      let a_inv_inv = a_inv.inverse().unwrap();
      assert_eq!(a_inv_inv, a);
    }
  }

  #[test]
  fn distributivity() {
    let a = GF17::new(5);
    let b = GF17::new(6);
    let c = GF17::new(7);
    assert_eq!((a * (b + c)).value, (a * b + a * c).value);
  }

  #[test]
  fn associativity() {
    let a = GF17::new(5);
    let b = GF17::new(6);
    let c = GF17::new(7);
    assert_eq!(((a + b) + c).value, (a + (b + c)).value);
    assert_eq!(((a * b) * c).value, (a * (b * c)).value);
  }

  #[test]
  fn non_zero_element() {
    let a = GF17::new(10);
    assert!(!(a == GF17::ZERO));
  }

  #[should_panic]
  #[test]
  fn not_primitive_root_of_unity() {
    let n = 3;
    let _omega = GF17::primitive_root_of_unity(n);
  }
}
