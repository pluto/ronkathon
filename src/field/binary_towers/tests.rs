use std::array;

use extension::BinaryFieldExtension;
use pretty_assertions::assert_eq;
use rstest::rstest;

use super::*;
use crate::{
  field::{
    binary_towers::extension::{multiply, num_digits, to_bool_vec},
    extension::ExtensionField,
    GaloisField,
  },
  polynomial::Monomial,
  Polynomial,
};

pub type TestBinaryField = PrimeField<2>;
pub type TestBinaryExtensionField = GaloisField<8, 2>;

impl FiniteField for TestBinaryExtensionField {
  const ONE: Self = Self::new([
    TestBinaryField::ONE,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
  ]);
  const ORDER: usize = TestBinaryField::ORDER.pow(8);
  const PRIMITIVE_ELEMENT: Self = Self::new([
    TestBinaryField::ONE,
    TestBinaryField::ONE,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
    TestBinaryField::ONE,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
  ]);
  const ZERO: Self = Self::new([
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
    TestBinaryField::ZERO,
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

impl ExtensionField<8, 2> for TestBinaryExtensionField {
  const IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS: [TestBinaryField; 9] = [
    TestBinaryField::ONE,  // 1
    TestBinaryField::ONE,  // a
    TestBinaryField::ZERO, // a^2
    TestBinaryField::ONE,  // a^3
    TestBinaryField::ONE,  // a^4
    TestBinaryField::ZERO, // a^5
    TestBinaryField::ZERO, // a^6
    TestBinaryField::ZERO, // a^7
    TestBinaryField::ONE,  // a^8
  ];
}

/// Returns the multiplication of two [`Ext<2, GF101>`] elements by reducing result modulo
/// irreducible polynomial.
impl Mul for TestBinaryExtensionField {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    let poly_self = Polynomial::<Monomial, TestBinaryField>::from(self);
    let poly_rhs = Polynomial::<Monomial, TestBinaryField>::from(rhs);
    let poly_irred =
      Polynomial::<Monomial, TestBinaryField>::from(Self::IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS);
    let product = (poly_self * poly_rhs) % poly_irred;
    let res: [TestBinaryField; 8] =
      array::from_fn(|i| product.coefficients.get(i).cloned().unwrap_or(TestBinaryField::ZERO));
    Self::new(res)
  }
}
impl MulAssign for TestBinaryExtensionField {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}
impl Product for TestBinaryExtensionField {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl Div for TestBinaryExtensionField {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().expect("invalid inverse") }
}

impl DivAssign for TestBinaryExtensionField {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs }
}

impl Rem for TestBinaryExtensionField {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
}

fn from_bool_vec(num: Vec<BinaryField>) -> u64 {
  let mut result: u64 = 0;
  for (i, &bit) in num.iter().rev().enumerate() {
    if bit.0 == 1 {
      result |= 1 << (num.len() - 1 - i);
    }
  }
  result
}

fn from_bool_vec_bin(num: Vec<TestBinaryField>) -> u64 {
  let mut result: u64 = 0;
  for (i, &bit) in num.iter().rev().enumerate() {
    if bit.value == 1 {
      result |= 1 << (num.len() - 1 - i);
    }
  }
  result
}

#[rstest]
#[case(0, 1)]
#[case(1, 1)]
#[should_panic]
#[case(1, 0)]
fn binary_field_arithmetic(#[case] a: usize, #[case] b: usize) {
  let arg1 = BinaryField::new(a as u8);
  let arg2 = BinaryField::new(b as u8);
  let a_test = TestBinaryField::new(a);
  let b_test = TestBinaryField::new(b);

  assert_eq!((arg1 + arg2).0, (a_test + b_test).value as u8);
  assert_eq!(arg1 - arg2, arg1 + arg2);
  assert_eq!((arg1 * arg2).0, (a_test * b_test).value as u8);

  let inv_res = arg2.inverse();
  assert!(inv_res.is_some());
  assert_eq!(inv_res.unwrap(), arg2);

  assert_eq!((arg1 / arg2).0, (a_test / b_test).value as u8);
}

#[rstest]
#[case(4, 3)]
#[case(9, 4)]
#[case(33, 6)]
#[case(67, 7)]
fn num_digit(#[case] num: u64, #[case] digits: usize) {
  assert_eq!(num_digits(num), digits);
}

#[test]
fn multiply_vec() {
  let a = [BinaryField::new(1)];
  let b = [BinaryField::new(1)];
  let res = multiply(&a, &b, 0);
  assert_eq!(res, vec![BinaryField::new(1)]);

  let a = to_bool_vec(160);
  let b = to_bool_vec(23);
  assert_eq!(a.len(), 8);
  assert_eq!(a.len(), b.len());

  assert_eq!(from_bool_vec(a.clone()), 160);
  assert_eq!(from_bool_vec(b.clone()), 23);

  let res = multiply(&a, &b, 3);
  let num = from_bool_vec(res);
  assert_eq!(num, 90);
}
