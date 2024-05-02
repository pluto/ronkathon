use core::{
  hash::{Hash, Hasher},
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign},
};
use std::fmt;

use num_bigint::BigUint;
use p3_field::{halve_u64, AbstractField, Field, Packable};
use serde::{Deserialize, Serialize};

const PLUTO_FIELD_PRIME: u64 = 101;
#[derive(Copy, Clone, Default, Serialize, Deserialize, Debug)]
pub struct PlutoField {
  value: u64,
}

impl PlutoField {
  pub const ORDER_U64: u64 = PLUTO_FIELD_PRIME;

  pub fn new(value: u64) -> Self { Self { value } }
}

impl PartialEq for PlutoField {
  fn eq(&self, other: &Self) -> bool {
    // TODO: removed canonicalization
    self.value == other.value
    // self.as_canonical_u64() == other.as_canonical_u64()
  }
}

impl fmt::Display for PlutoField {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.value) }
}

impl Eq for PlutoField {}
impl Packable for PlutoField {}

impl Div for PlutoField {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self { self * rhs.inverse() }
}
impl Field for PlutoField {
  // TODO: Add cfg-guarded Packing for AVX2, NEON, etc.
  type Packing = Self;

  fn is_zero(&self) -> bool { self.value == 0 || self.value == Self::ORDER_U64 }

  #[inline]
  fn exp_u64_generic<AF: AbstractField<F = Self>>(val: AF, _power: u64) -> AF {
    // TODO: Fix exponentiation
    val
    // match power {
    //     10540996611094048183 => exp_10540996611094048183(val), // used to compute x^{1/7}
    //     _ => exp_u64_by_squaring(val, power),
    // }
  }

  fn try_inverse(&self) -> Option<Self> {
    // TODO: Fix inverse
    Some(Self::new(1))
  }

  #[inline]
  fn halve(&self) -> Self { PlutoField::new(halve_u64::<PLUTO_FIELD_PRIME>(self.value)) }

  #[inline]
  fn order() -> BigUint { PLUTO_FIELD_PRIME.into() }
}

impl AbstractField for PlutoField {
  type F = Self;

  fn zero() -> Self { Self::new(0) }

  fn one() -> Self { Self::new(1) }

  fn two() -> Self { Self::new(2) }

  fn neg_one() -> Self { Self::new(Self::ORDER_U64 - 1) }

  #[inline]
  fn from_f(f: Self::F) -> Self { f }

  fn from_bool(b: bool) -> Self { Self::new(u64::from(b)) }

  fn from_canonical_u8(n: u8) -> Self { Self::new(u64::from(n)) }

  fn from_canonical_u16(n: u16) -> Self { Self::new(u64::from(n)) }

  fn from_canonical_u32(n: u32) -> Self { Self::new(u64::from(n)) }

  fn from_canonical_u64(n: u64) -> Self { Self::new(n) }

  fn from_canonical_usize(n: usize) -> Self { Self::new(n as u64) }

  fn from_wrapped_u32(n: u32) -> Self {
    // A u32 must be canonical, plus we don't store canonical encodings anyway, so there's no
    // need for a reduction.
    Self::new(u64::from(n))
  }

  fn from_wrapped_u64(n: u64) -> Self {
    // There's no need to reduce `n` to canonical form, as our internal encoding is
    // non-canonical, so there's no need for a reduction.
    Self::new(n)
  }

  // Sage: GF(2^64 - 2^32 + 1).multiplicative_generator()
  fn generator() -> Self { Self::new(7) }
}

impl Hash for PlutoField {
  fn hash<H: Hasher>(&self, state: &mut H) {
    state.write_u64(self.value);
    // state.write_u64(self.as_canonical_u64());
  }
}

// impl PrimeField for PlutoField {
//     fn as_canonical_biguint(&self) -> BigUint {
//         <Self as PrimeField32>::as_canonical_u32(self).into()
//     }
// }

// impl PrimeField64 for PlutoField {
//     const ORDER_U64: u64 = <Self as PrimeField32>::ORDER_U32 as u64;

//     #[inline]
//     fn as_canonical_u64(&self) -> u64 {
//         u64::from(self.as_canonical_u32())
//     }
// }

// impl PrimeField32 for PlutoField {
//     const ORDER_U32: u32 = P;

//     #[inline]
//     fn as_canonical_u32(&self) -> u32 {
//         from_monty(self.value)
//     }
// }

impl Mul for PlutoField {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self {
    // reduce128(u128::from(self.value) * u128::from(rhs.value))
    let mul = self.value * rhs.value;
    Self::new(mul)
  }
}

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

  fn neg(self) -> Self::Output {
    Self::new(Self::ORDER_U64 - self.value)
    // Self::new(Self::ORDER_U64 - self.as_canonical_u64())
  }
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
