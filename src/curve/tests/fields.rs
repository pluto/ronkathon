use core::ops::{Div, DivAssign, Mul, MulAssign, Rem};
use std::iter::Product;

use super::*;
use crate::algebra::field::extension::ExtensionField;
pub type TestField = PrimeField<59>;
pub type TestExtension = GaloisField<2, 59>;

impl Field for TestExtension {
  const ONE: Self = Self::new([TestField::ONE, TestField::ZERO]);
  const ZERO: Self = Self::new([TestField::ZERO, TestField::ZERO]);

  /// Computes the multiplicative inverse of `a`, i.e. 1 / (a0 + a1 * t).
  /// Multiply by `a0 - a1 * t` in numerator and denominator.
  /// Denominator equals `(a0 + a1 * t) * (a0 - a1 * t) = a0.pow(2) - a1.pow(2) * Q::residue()`
  fn inverse(&self) -> Option<Self> {
    if *self == Self::ZERO {
      return None;
    }

    let mut res = Self::default();
    let scalar =
      (self.coeffs[0].pow(2) + TestField::from(1u32) * self.coeffs[1].pow(2)).inverse().unwrap();
    res.coeffs[0] = self.coeffs[0] * scalar;
    res.coeffs[1] = -self.coeffs[1] * scalar;
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

impl ExtensionField<2, 59> for GaloisField<2, 59> {
  const IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS: [PrimeField<59>; 3] =
    [PrimeField::<59>::ONE, PrimeField::<59>::ZERO, PrimeField::<59>::ONE];
}

impl FiniteField for TestExtension {
  // TODO: This is not correct for this field!!! Fix!
  const PRIMITIVE_ELEMENT: Self = Self::new([TestField::new(14), TestField::new(9)]);
}

/// Returns the multiplication of two [`Ext<2, GF101>`] elements by reducing result modulo
/// irreducible polynomial.
impl Mul for TestExtension {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    let poly_self = Polynomial::<Monomial, TestField, 2>::from(self);
    let poly_rhs = Polynomial::<Monomial, TestField, 2>::from(rhs);
    let poly_irred =
      Polynomial::<Monomial, TestField, 3>::from(Self::IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS);
    let product = (poly_self * poly_rhs) % poly_irred;
    let res: [TestField; 2] =
      array::from_fn(|i| product.coefficients.get(i).cloned().unwrap_or(TestField::ZERO));
    Self::new(res)
  }
}

impl MulAssign for TestExtension {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}
impl Product for TestExtension {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl Div for TestExtension {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().expect("invalid inverse") }
}

impl DivAssign for TestExtension {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs }
}

impl Rem for TestExtension {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
}

#[cfg(test)]
mod tests {

  use super::*;

  #[test]
  fn i_squared() {
    let a = TestExtension::new([TestField::new(0), TestField::new(1)]);
    let b = TestExtension::new([TestField::new(0), TestField::new(1)]);
    let c = a * b;
    assert_eq!(c, TestExtension::new([TestField::new(TestField::ORDER - 1), TestField::new(0)]));
  }

  #[test]
  fn distorted_generator() {
    let x = TestExtension::new([-TestField::new(25), TestField::ZERO]);
    println!("x: {:?}", x);

    let y = TestExtension::new([TestField::ZERO, TestField::new(30)]);
    println!("y: {:?}", y);

    let x_cubed = x * x * x;
    println!("x^3: {:?}", x_cubed);

    let y_squared = y * y;
    println!("y^2: {:?}", y_squared);

    assert!(y_squared == x_cubed + x);
  }

  #[test]
  fn double_distorted_generator() {
    let x = TestExtension::new([-TestField::new(25), TestField::ZERO]);
    let y = TestExtension::new([TestField::ZERO, TestField::new(30)]);
    let point = AffinePoint::<TestCurveExtended>::new(x, y);
    let _doubled_point = point + point;
  }

  #[test]
  fn test_pow() {
    let x = TestExtension::new([TestField::new(43), TestField::new(52)]);
    let y = x.pow((59 * 59 - 1) / 5);
    assert_eq!(y, TestExtension::new([TestField::new(42), TestField::new(40)]));
  }
}
