//! This module contains the implementation of the finite field GF(101) and its arithmetic
//! operations.

use rand::distributions::{Distribution, Standard};

use super::*;

/// The prime number that defines the base prime-order finite field used throughout this crate.
pub const PLUTO_FIELD_PRIME: u32 = 101;

/// [`GF101`] represents the finite field GF(101) that has 101 elements and works with typical sum
/// and multiplication operations modulo 101.
#[derive(Copy, Clone, Default, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct GF101 {
  value: u32,
}

impl fmt::Display for GF101 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.value) }
}

impl GF101 {
  /// Create a new [`GF101`] element from the given value. The value is reduced modulo 101 to
  /// ensure it is within the field.
  pub const fn new(value: u32) -> Self { Self { value: value % PLUTO_FIELD_PRIME } }
}

impl FiniteField for GF101 {
  type Storage = u32;

  const NEG_ONE: Self = Self::new(Self::ORDER - 1);
  const ONE: Self = Self::new(1);
  const ORDER: Self::Storage = PLUTO_FIELD_PRIME;
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

impl Add for GF101 {
  type Output = Self;

  fn add(self, rhs: Self) -> Self { Self { value: (self.value + rhs.value) % Self::ORDER } }
}

impl AddAssign for GF101 {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl Sum for GF101 {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO)
  }
}

impl Sub for GF101 {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let (mut diff, over) = self.value.overflowing_sub(rhs.value);
    let corr = if over { Self::ORDER } else { 0 };
    diff = diff.wrapping_add(corr);
    Self { value: diff }
  }
}

impl SubAssign for GF101 {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl Mul for GF101 {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self { Self { value: (self.value * rhs.value) % Self::ORDER } }
}

impl MulAssign for GF101 {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl Product for GF101 {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl Div for GF101 {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self { self * rhs.inverse().unwrap() }
}

impl DivAssign for GF101 {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl Neg for GF101 {
  type Output = Self;

  fn neg(self) -> Self::Output { Self::ZERO - self }
}

impl Rem for GF101 {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self { self - (self / rhs) * rhs }
}

impl Distribution<GF101> for Standard {
  #[inline]
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> GF101 {
    loop {
      let next_u31 = rng.next_u32() >> 4;
      let is_canonical = next_u31 < GF101::ORDER;
      if is_canonical {
        return GF101 { value: next_u31 };
      }
    }
  }
}

impl From<u32> for GF101 {
  fn from(val: u32) -> Self { Self::new(val) }
}

impl From<u64> for GF101 {
  fn from(val: u64) -> Self { Self::new(val as u32) }
}

impl From<usize> for GF101 {
  fn from(val: usize) -> Self { Self::new(val as u32) }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn overflowing_add() {
    let a = GF101::new(100);
    let b = GF101::new(20);
    let c = a + b;
    assert_eq!(c, GF101::new(19));
  }

  #[test]
  fn underflow_sub() {
    let a = GF101::new(10);
    let b = GF101::new(20);
    let c = a - b;
    assert_eq!(c, GF101::new(91));
  }

  #[test]
  fn halve() {
    let a = GF101::new(10);
    assert_eq!(a, (a / GF101::TWO) * GF101::TWO);
  }

  #[test]
  fn overflowing_mul() {
    let a = GF101::new(10);
    let b = GF101::new(20);
    let c = a * b;
    assert_eq!(c, GF101::new(99));
  }

  #[test]
  fn zero() {
    let f = GF101::new(0);
    assert_eq!(f.value, 0);

    let f = GF101::new(GF101::ORDER);
    assert_eq!(f.value, 0);
  }

  #[test]
  fn exp_generic() {
    let f = GF101::new(2);
    let exp = f.pow(3);
    assert_eq!(exp, GF101::new(8));
  }

  #[test]
  fn addition_subtraction() {
    let a = GF101::new(50);
    let b = GF101::new(60);
    let c = a + b;
    assert_eq!(c, GF101::new(9)); // (50 + 60) % 101 = 9

    let d = c - a;
    assert_eq!(d, GF101::new(60)); // (9 - 50) % 101 = 60
  }

  #[test]
  fn add_sub_neg_mul() {
    let mut rng = rand::thread_rng();
    // for i in 0..1000 {
    let x = rng.gen::<GF101>();
    let y = rng.gen::<GF101>();
    let z = rng.gen::<GF101>();
    assert_eq!(x + (-x), GF101::ZERO);
    assert_eq!(-x, GF101::ZERO - x);
    assert_eq!(x + x, x * GF101::TWO);
    assert_eq!(x, x.div(GF101::new(2)) * GF101::TWO);
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
  fn multiplicative_inverse() {
    let a = GF101::new(10);
    let a_inv = a.inverse().unwrap();
    let should_be_one = a * a_inv;
    assert_eq!(should_be_one, GF101::new(1));
  }

  #[should_panic]
  #[test]
  fn no_zero_inverse() {
    let zero = GF101::new(0);
    let _inv = zero.inverse().unwrap();
  }

  #[test]
  fn identity_elements() {
    let a = GF101::new(10);
    let zero = GF101::new(0);
    let one = GF101::new(1);
    assert_eq!((a + zero).value, a.value);
    assert_eq!((a * one).value, a.value);
  }

  #[test]
  fn zero_multiplication() {
    let a = GF101::new(10);
    let zero = GF101::new(0);
    assert_eq!((a * zero).value, 0);
  }

  #[test]
  fn negation() {
    let a = GF101::new(10);
    let neg_a = -a;
    assert_eq!((a + neg_a).value, 0);
  }

  #[test]
  fn inverse_of_inverse() {
    let a = GF101::new(10);
    let a_inv = a.inverse().unwrap();
    let a_inv_inv = a_inv.inverse().unwrap();
    assert_eq!(a_inv_inv, a);
  }

  #[test]
  fn distributivity() {
    let a = GF101::new(5);
    let b = GF101::new(6);
    let c = GF101::new(7);
    assert_eq!((a * (b + c)).value, (a * b + a * c).value);
  }

  #[test]
  fn associativity() {
    let a = GF101::new(5);
    let b = GF101::new(6);
    let c = GF101::new(7);
    assert_eq!(((a + b) + c).value, (a + (b + c)).value);
    assert_eq!(((a * b) * c).value, (a * (b * c)).value);
  }

  #[test]
  fn non_zero_element() {
    let a = GF101::new(10);
    assert!(!(a == GF101::ZERO));
  }

  #[test]
  fn power_of_zero() {
    let a = GF101::new(0);
    let b = a.pow(3);
    assert_eq!(b.value, 0);
  }

  #[should_panic]
  #[test]
  fn not_primitive_root_of_unity() {
    let n = 3;
    let _omega = GF101::primitive_root_of_unity(n);
  }

  #[test]
  fn primitive_root_of_unity() {
    let n = 5;
    let omega = GF101::primitive_root_of_unity(n);
    println!("omega: {:?}", omega);
    assert_eq!(omega, GF101::new(95));
    let omega_n = omega.pow(n.into());
    for i in 1..n {
      let omega_i = omega.pow(i.into());
      println!("omega^{}: {:?}", i, omega_i);
      assert_ne!(omega_i, GF101::new(1));
    }
    assert_eq!(omega_n, GF101::new(1));

    let n = 25;
    let omega = GF101::primitive_root_of_unity(n);
    println!("omega: {:?}", omega);
    assert_eq!(omega, GF101::new(16));
    for i in 1..n {
      let omega_i = omega.pow(i.into());
      println!("omega^{}: {:?}", i, omega_i);
      assert_ne!(omega_i, GF101::new(1));
    }
    let omega_n = omega.pow(n.into());
    assert_eq!(omega_n, GF101::new(1));
  }

  #[test]
  fn polynomial_sum() {
    let a = GF101::new(1);
    let b = GF101::new(2);
    let c = GF101::new(3);
    let d = GF101::new(4);

    let n = 4;
    let omega = GF101::primitive_root_of_unity(n);

    let out = a + b * omega + c * omega.pow(2) + d * omega.pow(3);
    assert_eq!(out, GF101::new(79));
  }
}
