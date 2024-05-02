use core::{
  hash::{Hash, Hasher},
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign},
};
use std::fmt;

use num_bigint::BigUint;
use p3_field::{exp_u64_by_squaring, halve_u32, AbstractField, Field, Packable};
use serde::{Deserialize, Serialize};

const PLUTO_FIELD_PRIME: u32 = 101;
// const MONTY_BITS: u32 = 7;
// const MONTY_MASK: u32 = (1 << MONTY_BITS) - 1;
// const MONTY_MU: u32 = 80;

#[derive(Copy, Clone, Default, Serialize, Deserialize, Debug, Hash, PartialEq, Eq)]
pub struct PlutoField {
  value: u32,
}

impl PlutoField {
  pub const ORDER_U32: u32 = PLUTO_FIELD_PRIME;

  pub fn new(value: u32) -> Self { Self { value } }
}

impl fmt::Display for PlutoField {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.value) }
}

impl Packable for PlutoField {}

impl Div for PlutoField {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self { self * rhs.inverse() }
}
impl Field for PlutoField {
  // TODO: Add cfg-guarded Packing for AVX2, NEON, etc.
  type Packing = Self;

  fn is_zero(&self) -> bool { self.value == 0 || self.value == Self::ORDER_U32 }

  #[inline]
  fn exp_u64_generic<AF: AbstractField<F = Self>>(val: AF, power: u64) -> AF {
    exp_u64_by_squaring(val, power)
  }

  fn try_inverse(&self) -> Option<Self> {
    // TODO: Fix inverse
    Some(Self::new(1))
  }

  #[inline]
  fn halve(&self) -> Self { PlutoField::new(halve_u32::<PLUTO_FIELD_PRIME>(self.value)) }

  #[inline]
  fn order() -> BigUint { PLUTO_FIELD_PRIME.into() }
}

impl AbstractField for PlutoField {
  type F = Self;

  fn zero() -> Self { Self::new(0) }

  fn one() -> Self { Self::new(1) }

  fn two() -> Self { Self::new(2) }

  fn neg_one() -> Self { Self::new(Self::ORDER_U32 - 1) }

  #[inline]
  fn from_f(f: Self::F) -> Self { f }

  fn from_bool(b: bool) -> Self { Self::new(u32::from(b)) }

  fn from_canonical_u8(n: u8) -> Self { Self::new(u32::from(n)) }

  fn from_canonical_u16(n: u16) -> Self { Self::new(u32::from(n)) }

  fn from_canonical_u32(n: u32) -> Self { Self::new(n) }

  #[inline]
  fn from_canonical_u64(n: u64) -> Self {
    debug_assert!(n < PLUTO_FIELD_PRIME as u64);
    Self::from_canonical_u32(n as u32)
  }

  #[inline]
  fn from_canonical_usize(n: usize) -> Self {
    debug_assert!(n < PLUTO_FIELD_PRIME as usize);
    Self::from_canonical_u32(n as u32)
  }

  #[inline]
  fn from_wrapped_u32(n: u32) -> Self { Self { value: n % PLUTO_FIELD_PRIME } }

  #[inline]
  fn from_wrapped_u64(n: u64) -> Self { Self { value: (n % PLUTO_FIELD_PRIME as u64) as u32 } }

  // Sage: GF(2^64 - 2^32 + 1).multiplicative_generator()
  // TODO: Find a generator for this field
  fn generator() -> Self { Self::new(7) }
}

impl Mul for PlutoField {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self { Self { value: (self.value * rhs.value) % 101 } }
}

// /// Montgomery reduction of a value in `0..P << MONTY_BITS`.
// #[inline]
// #[must_use]
// pub(crate) const fn monty_reduce(x: u32) -> u32 {
//     let t = x.wrapping_mul(MONTY_MU) & (MONTY_MASK);
//     let u = (t * (PLUTO_FIELD_PRIME)) & (MONTY_MASK );

//     let (x_sub_u, over) = x.overflowing_sub(u);
//     let x_sub_u_hi = (x_sub_u >> MONTY_BITS) as u32;
//     let corr = if over { PLUTO_FIELD_PRIME } else { 0 };
//     x_sub_u_hi.wrapping_add(corr)
// }

impl Product for PlutoField {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::one())
  }
}

impl SubAssign for PlutoField {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl AddAssign for PlutoField {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl MulAssign for PlutoField {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl Neg for PlutoField {
  type Output = Self;

  fn neg(self) -> Self::Output { Self::new(Self::ORDER_U32 - self.value) }
}

impl Add for PlutoField {
  type Output = Self;

  fn add(self, rhs: Self) -> Self {
    let mut sum = self.value + rhs.value;
    let (corr_sum, over) = sum.overflowing_sub(PLUTO_FIELD_PRIME);
    if !over {
      sum = corr_sum;
    }
    Self { value: sum }
  }
}

impl Sum for PlutoField {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(Self::zero())
  }
}

impl Sub for PlutoField {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let (mut diff, over) = self.value.overflowing_sub(rhs.value);
    let corr = if over { PLUTO_FIELD_PRIME } else { 0 };
    diff = diff.wrapping_add(corr);
    Self::new(diff)
  }
}

// #[inline]
// #[must_use]
// const fn to_monty(x: u32) -> u32 {
//     (((x as u64) << MONTY_BITS) % PLUTO_FIELD_PRIME as u64) as u32
// }

// #[inline]
// #[must_use]
// const fn to_monty_64(x: u64) -> u32 {
//     (((x as u128) << MONTY_BITS) % PLUTO_FIELD_PRIME as u128) as u32
// }

mod tests {
  use super::*;

  type F = PlutoField;

  #[test]
  fn test_overflowing_add() {
    let a = PlutoField::new(100);
    let b = PlutoField::new(20);
    let c = a + b;
    assert_eq!(c.value, 19);
  }

  #[test]
  fn underflow_sub() {
    let a = PlutoField::new(10);
    let b = PlutoField::new(20);
    let c = a - b;
    assert_eq!(c.value, 91);
  }

  #[test]
  fn overflowing_mul() {
    let a = PlutoField::new(10);
    let b = PlutoField::new(20);
    let c = a * b;
    println!("c: {:?}", c);
    assert_eq!(c.value, 99);
  }

  #[test]
  fn zero() {
    let f = F::from_canonical_u32(0);
    assert!(f.is_zero());

    let f = F::from_wrapped_u32(F::ORDER_U32);
    assert!(f.is_zero());
  }

  #[test]
  fn exp_u64_generic() {
    let f = F::from_canonical_u32(2);
    let f = F::exp_u64_generic(f, 3);
    assert_eq!(f, F::from_canonical_u32(8));
  }
}
