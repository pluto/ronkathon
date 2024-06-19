//! Contains implementation of binary field and extension fields
use std::{
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign},
};

use crate::field::FiniteField;

pub mod extension;
pub use extension::BinaryTowers;

#[cfg(test)] mod tests;

/// binary field containing element `{0,1}`
#[derive(Debug, Default, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct BinaryField(u8);

impl BinaryField {
  /// create new binary field element
  pub const fn new(value: u8) -> Self {
    debug_assert!(value < 2, "value should be less than 2");
    Self(value)
  }
}

impl FiniteField for BinaryField {
  const ONE: Self = BinaryField(1);
  const ORDER: usize = 2;
  const PRIMITIVE_ELEMENT: Self = Self::ONE;
  const ZERO: Self = BinaryField(0);

  fn inverse(&self) -> Option<Self> {
    if *self == Self::ZERO {
      return None;
    }
    Some(*self)
  }

  fn pow(self, _: usize) -> Self { self }
}

impl From<usize> for BinaryField {
  fn from(value: usize) -> Self { Self::new(value as u8) }
}

impl Add for BinaryField {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn add(self, rhs: Self) -> Self::Output { BinaryField::new(self.0 ^ rhs.0) }
}

impl AddAssign for BinaryField {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl Sum for BinaryField {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO)
  }
}

impl Sub for BinaryField {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn sub(self, rhs: Self) -> Self::Output { BinaryField(self.0 ^ rhs.0) }
}

impl SubAssign for BinaryField {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl Neg for BinaryField {
  type Output = Self;

  fn neg(self) -> Self::Output { self }
}

impl Mul for BinaryField {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn mul(self, rhs: Self) -> Self::Output { BinaryField(self.0 & rhs.0) }
}

impl MulAssign for BinaryField {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl Product for BinaryField {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl Div for BinaryField {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().unwrap() }
}

impl DivAssign for BinaryField {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl Rem for BinaryField {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
}
