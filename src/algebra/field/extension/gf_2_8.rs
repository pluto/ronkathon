//! This module contains an implementation of the quadratic extension field GF(2^8).
//! Elements represented as coefficients of a [`Polynomial`] in the [`Monomial`] basis of degree 1
//! in form: `a_0 + a_1*t`` where {a_0, a_1} \in \mathhbb{F}. Uses irreducible poly of the form:
//! (X^2-K).
//!
//! This extension field is used for our [AES implementation][`crate::encryption::symmetric::aes`].
use super::{prime::AESField, *};
use crate::{Monomial, Polynomial};

impl Field for GaloisField<8, 2> {
  const ONE: Self = Self::new([
    AESField::ONE,
    AESField::ZERO,
    AESField::ZERO,
    AESField::ZERO,
    AESField::ZERO,
    AESField::ZERO,
    AESField::ZERO,
    AESField::ZERO,
  ]);
  const ZERO: Self = Self::new([
    AESField::ZERO,
    AESField::ZERO,
    AESField::ZERO,
    AESField::ZERO,
    AESField::ZERO,
    AESField::ZERO,
    AESField::ZERO,
    AESField::ZERO,
  ]);

  /// Computes the multiplicative inverse of `a`, i.e. 1 / (a0 + a1 * t).
  fn inverse(&self) -> Option<Self> {
    if *self == Self::ZERO {
      return None;
    }

    let res = self.pow(Self::ORDER - 2);
    Some(res)
  }

  fn pow(self, power: usize) -> Self {
    if power == 0 {
      Self::ONE
    } else if power == 1 {
      self
    } else if power % 2 == 0 {
      self.pow(power / 2) * self.pow(power / 2)
    } else {
      self.pow(power / 2) * self.pow(power / 2) * self
    }
  }
}

impl FiniteField for GaloisField<8, 2> {
  const PRIMITIVE_ELEMENT: Self = Self::new([
    AESField::ONE,
    AESField::ONE,
    AESField::ZERO,
    AESField::ZERO,
    AESField::ONE,
    AESField::ZERO,
    AESField::ZERO,
    AESField::ZERO,
  ]);
}

impl ExtensionField<8, 2> for GaloisField<8, 2> {
  /// Represents the irreducible polynomial x^8 + x^4 + x^3 + x + 1.
  const IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS: [AESField; 9] = [
    AESField::ONE,  // 1
    AESField::ONE,  // a
    AESField::ZERO, // a^2
    AESField::ONE,  // a^3
    AESField::ONE,  // a^4
    AESField::ZERO, // a^5
    AESField::ZERO, // a^6
    AESField::ZERO, // a^7
    AESField::ONE,  // a^8
  ];
}

/// Returns the multiplication of two [`Ext<8, GF2>`] elements by reducing result modulo
/// irreducible polynomial.
impl Mul for GaloisField<8, 2> {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    let poly_self = Polynomial::<Monomial, AESField, 8>::from(self);
    let poly_rhs = Polynomial::<Monomial, AESField, 8>::from(rhs);
    let poly_irred =
      Polynomial::<Monomial, AESField, 9>::from(Self::IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS);
    let product = (poly_self * poly_rhs) % poly_irred;
    let res: [AESField; 8] =
      array::from_fn(|i| product.coefficients.get(i).cloned().unwrap_or(AESField::ZERO));
    Self::new(res)
  }
}
impl MulAssign for GaloisField<8, 2> {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}
impl Product for GaloisField<8, 2> {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl Div for GaloisField<8, 2> {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().expect("invalid inverse") }
}

impl DivAssign for GaloisField<8, 2> {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs }
}

impl Rem for GaloisField<8, 2> {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
}
