use core::{
  hash::{Hash, Hasher},
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign},
};
use std::fmt;

use num_bigint::BigUint;
use rand::{
  distributions::{Distribution, Standard},
  Rng,
};
use serde::{Deserialize, Serialize};

use super::*;

const PLUTO_FIELD_PRIME: u32 = 101;
// value chosen such that 2^k is closest power of two from modulus
const MONTY_BITS: u32 = 7;
// mask used in (mod R) operation for montgomery reduciton
const MONTY_MASK: u32 = (1 << MONTY_BITS) - 1;
// (-P^-1) mod 2^MONTY_BITS
const MONTY_MU: u32 = 19;

#[derive(Copy, Clone, Default, Serialize, Deserialize, Debug, Hash, PartialEq, Eq)]
pub struct GF101 {
  value: u32,
}

impl fmt::Display for GF101 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.value) }
}

impl GF101 {
  pub const fn new(value: u32) -> Self { Self { value: to_monty(value) } }
}

impl FiniteField for GF101 {
  type Storage = u32;

  const ORDER: Self::Storage = PLUTO_FIELD_PRIME;

  fn inverse(&self) -> Option<Self> {
    if self.value == 0 {
      return None;
    }
    let exponent = Self::ORDER - 2;
    let mut result = Self::one();
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

  fn zero() -> Self { Self::new(0) }

  fn one() -> Self { Self::new(1) }

  fn two() -> Self { Self::new(2) }

  fn neg_one() -> Self { Self::new(Self::ORDER - 1) }

  fn generator() -> Self { Self::new(2) }

  fn from_canonical_u32(n: u32) -> Self { Self::new(n) }
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
    iter.reduce(|x, y| x + y).unwrap_or(Self::zero())
  }
}

impl Sub for GF101 {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let (mut diff, over) = self.value.overflowing_sub(rhs.value);
    let corr = if over { PLUTO_FIELD_PRIME } else { 0 };
    diff = diff.wrapping_add(corr);
    Self { value: diff }
  }
}

impl SubAssign for GF101 {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl Mul for GF101 {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self { Self { value: from_monty(self.value * rhs.value) } }
}

impl MulAssign for GF101 {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl Product for GF101 {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::one())
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

  fn neg(self) -> Self::Output { Self::zero() - self }
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
      let is_canonical = next_u31 < PLUTO_FIELD_PRIME;
      if is_canonical {
        return GF101 { value: next_u31 };
      }
    }
  }
}

#[must_use]
#[inline]
/// Converts a number to montgomery form: \bar{x} := x * R mod N.
/// R is chosen such that gcd(R, N) = 1, usually nearest 2^k to N.
///
/// Arithmetic in finite fields involves mod N operation which involves
/// division, a very costly operation as compared to other arithmetic operations.
/// But, division by 2^k only involves shifting right by `k` bits. Aim of montgomery
/// form is to make resulting number divisible by 2^k.
const fn to_monty(val: u32) -> u32 {
  (((val as u64) << MONTY_BITS) % PLUTO_FIELD_PRIME as u64) as u32
}

#[must_use]
#[inline]
/// Computes x*R^{-1} mod N.
/// Assumes: `x` is in montgomery form
///
/// Add such a multiple `m` of `N` such that `x` is divisible by `R` implies (x + mN) % R^{-1} = 0.
/// So, m = x*(-N)^{-1} % R satisfies above relation. Precompute N' = (-N)^{-1} mod R.
/// - Precompute: N' = (-N)^{-1}
/// - m = x*N' mod R (1 mult)
/// - u = m*N (1 mult)
/// - t = x+u mod R
/// - t \in [0, 2P), subtract N if t >= N
///
/// Montgomery arithmetic allows to perform modular multiplication in 3 mults, 2 mults per
/// reduction, and some bit shifts and masks since R is a power of 2, saving a costly division.
///
/// # Examples
/// ```ignore
/// let N = 101;
/// let a = to_monty(10);
/// let b = to_monty(20);
/// let c = from_monty(a * b);
/// assert_eq!(from_monty(c), 99);
/// ```
fn from_monty(x: u32) -> u32 {
  let x = x as u64;
  let m = x.wrapping_mul(MONTY_MU as u64) & (MONTY_MASK as u64); // x*N' % R
  let u = m * (PLUTO_FIELD_PRIME as u64); // m*P
  let t = ((x + u) >> MONTY_BITS) as u32; // x+mP / R
  let corr = if t >= PLUTO_FIELD_PRIME { PLUTO_FIELD_PRIME } else { 0 };
  t.wrapping_sub(corr)
}

// β=2^7
// I=β^2/N
const INV_APPROX: u32 = (1 << (2 * MONTY_BITS)) / PLUTO_FIELD_PRIME;

#[must_use]
#[inline]
/// Adapted from [Algorithm 1](https://hackmd.io/@chaosma/SyAvcYFxh).
///
/// Computes x mod N using barret reduction method. Assumes x < N^2.
/// Modular reduction involves division by N, barret's method approximates
/// value of 1/N with m/2^k so that costly division operation is substituted with
/// bit shifts. 2^2k is used because x < n*n < 2^k * 2^k. This allows to approximate
/// value of q closer to x/n.
///
/// x = q*N + r => r = x-qN => q = x/N => approximate q as ⌊m/2^2k⌋ => approximate m as ⌊2^2k/N⌋
///
/// - Precompute: I = ⌊2^{2k}/N⌋. floor is used as approximation function, implicitly used in
///   division
/// - q = x*I / 2^2k. divide by 2^{2k} again to approximate a value closer to 1/N
/// - r = x-qN
/// - r \in [0, 2P), subtract N if t >= N
///
/// # Examples
/// ```ignore
/// let x = 200 * 10;
/// let res = barret_reduction(x);
/// assert_eq!(res, x % PLUTO_FIELD_PRIME);
/// ```
fn barret_reduction(x: u32) -> u32 {
  assert!(x < (PLUTO_FIELD_PRIME.pow(2)));
  let q = (x * INV_APPROX) >> (2 * MONTY_BITS); // q = ⌊x*I/β^2⌋
  let r = x - (q * PLUTO_FIELD_PRIME); // t = x - q*N
  let corr = if r >= PLUTO_FIELD_PRIME { PLUTO_FIELD_PRIME } else { 0 };
  r.wrapping_sub(corr)
}

mod tests {
  use rand::{thread_rng, Rng};

  use super::*;

  type F = GF101;

  #[test]
  fn test_overflowing_add() {
    let a = F::new(100);
    let b = F::new(20);
    let c = a + b;
    assert_eq!(c, F::new(19));
  }

  #[test]
  fn underflow_sub() {
    let a = F::new(10);
    let b = F::new(20);
    let c = a - b;
    assert_eq!(c, F::new(91));
  }

  #[test]
  fn halve() {
    let a = F::new(10);
    assert_eq!(a, (a / F::two()) * F::two());
  }

  #[test]
  fn overflowing_mul() {
    let a = F::new(10);
    let b = F::new(20);
    let c = a * b;
    assert_eq!(c, F::new(99));
  }

  #[test]
  fn test_barret_reduction() {
    let x = 200 * 10;
    let res = barret_reduction(x);
    assert_eq!(res, x % PLUTO_FIELD_PRIME);
  }

  #[test]
  fn zero() {
    let f = F::new(0);
    assert_eq!(f.value, 0);

    let f = F::new(F::ORDER);
    assert_eq!(f.value, 0);
  }

  #[test]
  fn exp_generic() {
    let f = F::new(2);
    let exp = f.pow(3);
    assert_eq!(exp, F::new(8));
  }

  #[test]
  fn addition_subtraction() {
    let a = GF101::new(50);
    let b = GF101::new(60);
    let c = a + b;
    assert_eq!(c, F::new(9)); // (50 + 60) % 101 = 9

    let d = c - a;
    assert_eq!(d, F::new(60)); // (9 - 50) % 101 = 60
  }

  #[test]
  fn test_add_sub_neg_mul() {
    let mut rng = rand::thread_rng();
    // for i in 0..1000 {
    let x = rng.gen::<F>();
    let y = rng.gen::<F>();
    let z = rng.gen::<F>();
    assert_eq!(x + (-x), F::zero());
    assert_eq!(-x, F::zero() - x);
    assert_eq!(x + x, x * F::two());
    assert_eq!(x, x.div(F::new(2)) * F::two());
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
    assert_eq!(should_be_one, F::new(1));
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
    assert!(!(a == F::zero()));
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
    let omega = GF101::primitive_root_of_unity(n);
  }

  #[test]
  fn primitive_root_of_unity() {
    let n = 5;
    let omega = GF101::primitive_root_of_unity(n);
    println!("omega: {:?}", omega);
    assert_eq!(omega, F::new(95));
    let omega_n = omega.pow(n);
    for i in 1..n {
      let omega_i = omega.pow(i);
      println!("omega^{}: {:?}", i, omega_i);
      assert_ne!(omega_i, F::new(1));
    }
    assert_eq!(omega_n, F::new(1));

    let n = 25;
    let omega = GF101::primitive_root_of_unity(n);
    println!("omega: {:?}", omega);
    assert_eq!(omega, F::new(16));
    for i in 1..n {
      let omega_i = omega.pow(i);
      println!("omega^{}: {:?}", i, omega_i);
      assert_ne!(omega_i, F::new(1));
    }
    let omega_n = omega.pow(n);
    assert_eq!(omega_n, F::new(1));
  }
}
