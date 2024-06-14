//! Contains implementation of binary field and its extensions
// TODO:
// - move gf2k to const K, and use slices
// - move arithmetics out of binary
// - rename gf to binary field, and binary field extensions
// - more tests and docs
// -

use std::{
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign},
};

use super::FiniteField;

/// binary field containing element `{0,1}`
#[derive(Debug, Default, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct BinaryField(u8);

impl BinaryField {
  const fn new(value: u8) -> Self {
    debug_assert!(value < 2, "value should be less than 2");
    Self(value)
  }
}

impl FiniteField for BinaryField {
  const ONE: Self = BinaryField(1);
  const ORDER: usize = 2;
  // TODO: incorrect
  const PRIMITIVE_ELEMENT: Self = Self::ONE;
  const ZERO: Self = BinaryField(0);

  fn inverse(&self) -> Option<Self> { Some(*self) }

  fn pow(self, _: usize) -> Self { self }

  fn primitive_root_of_unity(_: usize) -> Self { Self::ONE }
}

impl From<usize> for BinaryField {
  fn from(value: usize) -> Self { Self::new(value as u8) }
}

impl Add for BinaryField {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn add(self, rhs: Self) -> Self::Output { BinaryField(self.0 ^ rhs.0) }
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

/// Binary extension field GF_{2^{2^K}} using binary towers
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct BinaryFieldExtension<const K: usize>
where [(); 1 << K]: {
  /// coefficients of field element
  pub coefficients: [BinaryField; 1 << K],
}

impl<const K: usize> BinaryFieldExtension<K>
where [(); 1 << K]:
{
  fn new(value: Vec<BinaryField>) -> Self {
    // debug_assert_eq!(value.len(), 1 << K);
    let mut coeffs = value.clone();
    let length = 1 << K;
    coeffs.extend(std::iter::repeat(BinaryField::ZERO).take(length - value.len()));

    let coeffs = coeffs.try_into().unwrap_or_else(|v: Vec<BinaryField>| {
      panic!("Expected a Vec of length {} but it was {}", 1 << K, v.len())
    });
    Self { coefficients: coeffs }
  }

  const fn one() -> Self {
    let mut coefficients = [BinaryField(0); 1 << K];
    coefficients[0] = BinaryField(1);
    BinaryFieldExtension { coefficients }
  }
}

impl<const K: usize> FiniteField for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  const ONE: Self = Self::one();
  const ORDER: usize = 1 << (1 << K);
  const PRIMITIVE_ELEMENT: Self = Self::one();
  const ZERO: Self = Self::default();

  fn pow(self, power: usize) -> Self {
    let mut result = BinaryFieldExtension::one();
    let mut base = self;
    let mut exp = power;

    while exp > 0 {
      if exp % 2 == 1 {
        result *= base;
      }
      base *= base;
      exp /= 2;
    }

    result
  }

  fn inverse(&self) -> Option<Self> { todo!() }
}

// Function to find a primitive element
// const fn find_primitive_element<const K: usize>() -> GF2k<K>
// where [(); 1 << K]: {
//   let mut candidate = GF2k::<K>::one();
//   let order = GF2k::<K>::ORDER;

//   loop {
//     let mut is_primitive = true;

//     for i in 1..order {
//       if candidate.pow(i) == GF2k::<K>::one() {
//         is_primitive = false;
//         break;
//       }
//     }

//     if is_primitive {
//       return candidate;
//     }

//     // Increment candidate
//     for coef in candidate.coefficients.iter_mut() {
//       if coef.0 == 0 {
//         *coef = GF2(1);
//         break;
//       } else {
//         *coef = GF2(0);
//       }
//     }
//   }
// }

impl<const K: usize> Default for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  fn default() -> Self { Self { coefficients: [BinaryField::new(0); 1 << K] } }
}

impl<const K: usize> Add for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    let result: [BinaryField; 1 << K] = self
      .coefficients
      .into_iter()
      .zip(rhs.coefficients)
      .map(|(a, b)| a + b)
      .collect::<Vec<BinaryField>>()
      .try_into()
      .unwrap_or_else(|v: Vec<BinaryField>| {
        panic!("Expected a Vec of length {} but it was {}", 1 << K, v.len())
      });
    Self { coefficients: result }
  }
}

impl<const K: usize> AddAssign for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<const K: usize> Sum for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(Self::default())
  }
}

impl<const K: usize> Sub for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn sub(self, rhs: Self) -> Self::Output { self + rhs }
}

impl<const K: usize> SubAssign for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<const K: usize> Mul for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    BinaryFieldExtension::<K>::new(multiply(
      self.coefficients.to_vec(),
      rhs.coefficients.to_vec(),
      K,
    ))
  }
}

impl<const K: usize> MulAssign for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<const K: usize> Product for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::one())
  }
}

impl<const K: usize> Neg for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  type Output = Self;

  fn neg(self) -> Self::Output { self }
}

impl<const K: usize> Div for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().unwrap() }
}

impl<const K: usize> DivAssign for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl<const K: usize> Rem for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  type Output = Self;

  fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
}

fn num_digits(n: u64) -> usize {
  let r = format!("{:b}", n);
  r.len()
}

fn to_bool_vec(mut num: u64) -> Vec<BinaryField> {
  let length = 1 << num_digits((num_digits(num) - 1) as u64);
  let mut result = Vec::new();
  while num > 0 {
    result.push(BinaryField::new(((num & 1) != 0) as u8));
    num >>= 1;
  }
  result.extend(std::iter::repeat(BinaryField::new(0)).take(length - result.len()));
  result
}

impl<const K: usize> From<usize> for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  fn from(value: usize) -> Self {
    let coefficients =
      to_bool_vec(value as u64).try_into().unwrap_or_else(|v: Vec<BinaryField>| {
        panic!("Expected a Vec of length {} but it was {}", 1 << K, v.len())
      });
    Self { coefficients }
  }
}

impl<const K: usize> From<BinaryFieldExtension<K>>
  for (BinaryFieldExtension<{ K - 1 }>, BinaryFieldExtension<{ K - 1 }>)
where
  [(); 1 << K]:,
  [(); 1 << { K - 1 }]:,
{
  fn from(value: BinaryFieldExtension<K>) -> Self {
    debug_assert!(K > 1, "K cannot be less than 1");
    let (lhs, rhs) = value.coefficients.split_at(value.coefficients.len());
    let lhs = BinaryFieldExtension::<{ K - 1 }>::new(lhs.to_vec());
    let rhs = BinaryFieldExtension::<{ K - 1 }>::new(rhs.to_vec());
    (lhs, rhs)
  }
}

impl<const K: usize> From<(BinaryFieldExtension<K>, BinaryFieldExtension<K>)>
  for BinaryFieldExtension<{ K + 1 }>
where
  [(); 1 << K]:,
  [(); 1 << { K + 1 }]:,
{
  fn from(value: (BinaryFieldExtension<{ K }>, BinaryFieldExtension<{ K }>)) -> Self {
    let coefficients = value.0.coefficients;
    let rhs_coefficients = value.1.coefficients;
    let result = [coefficients, rhs_coefficients].concat();
    BinaryFieldExtension::<{ K + 1 }>::new(result)
  }
}

fn multiply(v1: Vec<BinaryField>, v2: Vec<BinaryField>, k: usize) -> Vec<BinaryField> {
  debug_assert!(v1.len() == v2.len(), "v1 and v2 should be of same size");

  if k == 0 {
    let res = v1[0] * v2[0];
    return vec![res];
  }

  let halflen = v1.len() / 2;
  let quarterlen = halflen / 2;

  let (l1, r1) = v1.split_at(halflen);
  let (l2, r2) = v2.split_at(halflen);

  let l1l2 = multiply(l1.to_vec(), l2.to_vec(), k - 1);
  let r1r2 = multiply(r1.to_vec(), r2.to_vec(), k - 1);

  let z3 = multiply(add_vec(l1.to_vec(), r1.to_vec()), add_vec(l2.to_vec(), r2.to_vec()), k - 1);

  let mut k2_val = vec![BinaryField::new(0); 1 << (k - 1)];
  k2_val[quarterlen] = BinaryField::new(1);

  let r1r2_high = multiply(k2_val, r1r2.clone(), k - 1);
  let mut res_low = add_vec(l1l2.clone(), r1r2.clone());
  let res_high = add_vec(z3, l1l2);
  let res_high = add_vec(res_high, r1r2);
  let mut res_high = add_vec(res_high, r1r2_high);
  res_low.append(&mut res_high);

  res_low
}

fn add_vec(lhs: Vec<BinaryField>, rhs: Vec<BinaryField>) -> Vec<BinaryField> {
  lhs.into_iter().zip(rhs).map(|(a, b)| a + b).collect()
}

#[cfg(test)]
mod tests {
  use super::*;

  fn from_bool_vec(num: Vec<BinaryField>) -> u64 {
    let mut result: u64 = 0;
    for (i, &bit) in num.iter().rev().enumerate() {
      if bit.0 == 1 {
        result |= 1 << (num.len() - 1 - i);
      }
    }
    result
  }

  #[test]
  fn field_arithmetic() {
    let a = BinaryField::new(0);
    let b = BinaryField::new(1);
    let c = a + b;
    assert_eq!(c, b);
  }

  #[test]
  fn test_num_digits() {
    let digits = num_digits(4);
    assert_eq!(digits, 3);
  }

  #[test]
  fn multiply_vec() {
    let a = vec![BinaryField::new(1)];
    let b = vec![BinaryField::new(1)];
    let res = multiply(a, b, 0);
    assert_eq!(res, vec![BinaryField::new(1)]);

    let a = to_bool_vec(160);
    let b = to_bool_vec(23);
    assert_eq!(a.len(), 8);
    assert_eq!(a.len(), b.len());
    println!("{:?}", a);

    assert_eq!(from_bool_vec(a.clone()), 160);
    assert_eq!(from_bool_vec(b.clone()), 23);

    let res = multiply(a, b, 3);
    let num = from_bool_vec(res);
    println!("{}", num);
  }
}
