//! Contains implementation of binary field and extension fields
use std::{
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign},
};

use super::*;

pub mod extension;
pub use extension::BinaryTowers;

#[cfg(test)] mod tests;

/// binary field containing element `{0,1}`
#[derive(Debug, Default, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinaryField {
  /// binary field element `0`
  #[default]
  Zero,
  /// binary field element `1`
  One,
}

impl Finite for BinaryField {
  const ORDER: usize = 2;
}

impl Field for BinaryField {
  const ONE: Self = BinaryField::One;
  const ZERO: Self = BinaryField::Zero;

  fn inverse(&self) -> Option<Self> {
    match *self {
      Self::Zero => None,
      Self::One => Some(Self::One),
    }
  }

  fn pow(self, _: usize) -> Self { self }
}

impl FiniteField for BinaryField {
  const PRIMITIVE_ELEMENT: Self = Self::ONE;
}

impl From<usize> for BinaryField {
  fn from(value: usize) -> Self {
    match value {
      0 => BinaryField::Zero,
      1 => BinaryField::One,
      _ => panic!("Invalid `usize` value. Must be 0 or 1."),
    }
  }
}

impl Add for BinaryField {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn add(self, rhs: Self) -> Self::Output {
    if self == rhs {
      Self::ZERO
    } else {
      Self::ONE
    }
  }
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
  fn sub(self, rhs: Self) -> Self::Output {
    if self == rhs {
      Self::ZERO
    } else {
      Self::ONE
    }
  }
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
  fn mul(self, rhs: Self) -> Self::Output {
    match (self, rhs) {
      (Self::One, Self::One) => Self::ONE,
      _ => Self::ZERO,
    }
  }
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
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().expect("divide by zero") }
}

impl DivAssign for BinaryField {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl Rem for BinaryField {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
}
