use core::{
  iter::{Product, Sum},
  ops::{Add, AddAssign, Mul, Neg, Sub, SubAssign},
};
use std::ops::{Div, DivAssign, MulAssign, Rem};

use serde::{Deserialize, Serialize};

use crate::field::FiniteField;

const EXT_DEGREE: usize = 2;
const QUADRATIC_EXTENSION_FIELD_ORDER: u32 = 10201;

#[derive(Clone, Default, Copy, Eq, PartialEq, Hash, Debug, Serialize, Deserialize)]

pub struct QuadraticExtensionField<F: FiniteField> {
  pub(crate) value: [F; 2],
}

impl<F: FiniteField> QuadraticExtensionField<F> {
  const D: usize = 2;

  fn residue() -> F { F::from_canonical_u32(2) }
}

impl<F: FiniteField> FiniteField for QuadraticExtensionField<F> {
  type Storage = u32;

  const ORDER: Self::Storage = QUADRATIC_EXTENSION_FIELD_ORDER;

  fn zero() -> Self { Self { value: [F::zero(); EXT_DEGREE] } }

  fn one() -> Self { Self { value: [F::one(); EXT_DEGREE] } }

  fn two() -> Self { Self { value: [F::two(); EXT_DEGREE] } }

  fn neg_one() -> Self { Self { value: [F::neg_one(); EXT_DEGREE] } }

  fn generator() -> Self { Self { value: [F::from_canonical_u32(15), F::from_canonical_u32(20)] } }

  fn inverse(&self) -> Option<Self> {
    if *self == Self::zero() {
      return None;
    }

    let mut res = Self::default();
    let scalar =
      (self.value[0].square() - Self::residue() * self.value[1].square()).inverse().unwrap();
    res.value[0] = self.value[0] * scalar;
    res.value[1] = -self.value[1] * scalar;
    Some(res)
  }

  #[inline]
  fn pow(&self, power: Self::Storage) -> Self {
    // TODO: not ideal to duplicate across traits impls
    let mut current = *self;
    let power = power as u64;
    let mut product = Self::one();

    for j in 0..(64 - power.leading_zeros()) as usize {
      if (power >> j & 1) != 0 {
        product *= current;
      }
      current = current * current;
    }
    product
  }

  fn primitive_root_of_unity(n: Self::Storage) -> Self { todo!() }

  fn from_canonical_u32(n: u32) -> Self { Self { value: [F::from_canonical_u32(n), F::zero()] } }
}

impl<F: FiniteField> Add for QuadraticExtensionField<F> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    let mut res = self.value;
    for (r, rhs_val) in res.iter_mut().zip(rhs.value) {
      *r += rhs_val;
    }

    Self { value: res }
  }
}

impl<F: FiniteField> AddAssign for QuadraticExtensionField<F> {
  fn add_assign(&mut self, rhs: Self) { *self = self.clone() + rhs; }
}

impl<F: FiniteField> Sub for QuadraticExtensionField<F> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let mut res = self.value;
    for (r, rhs_val) in res.iter_mut().zip(rhs.value) {
      *r -= rhs_val;
    }

    Self { value: res }
  }
}

impl<F: FiniteField> SubAssign for QuadraticExtensionField<F> {
  fn sub_assign(&mut self, rhs: Self) { *self = self.clone() - rhs; }
}

impl<F: FiniteField> Sum for QuadraticExtensionField<F> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(Self::zero())
  }
}

impl<F: FiniteField> Product for QuadraticExtensionField<F> {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::one())
  }
}

impl<F: FiniteField> Mul for QuadraticExtensionField<F> {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    let a = self.value;
    let b = rhs.value;
    let mut res = Self::default();
    res.value[0] = a[0].clone() * b[0].clone() + a[1].clone() * a[1].clone() * Self::residue();
    res.value[1] = a[0].clone() * b[1].clone() + a[1].clone() * b[0].clone();
    res
  }
}

impl<F: FiniteField> MulAssign for QuadraticExtensionField<F> {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<F: FiniteField> Div for QuadraticExtensionField<F> {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().expect("invalid inverse") }
}

impl<F: FiniteField> DivAssign for QuadraticExtensionField<F> {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs }
}

impl<F: FiniteField> Neg for QuadraticExtensionField<F> {
  type Output = Self;

  fn neg(self) -> Self::Output { Self::zero() - self }
}

impl<F: FiniteField> Rem for QuadraticExtensionField<F> {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
}
