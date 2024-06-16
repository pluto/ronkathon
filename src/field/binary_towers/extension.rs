//! contains implementation of binary extension fields using tower field arithmetic in multilinear basis as defined in [DP23b](https://eprint.iacr.org/2023/1784.pdf)
use std::{
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign},
};

use super::BinaryField;
use crate::field::FiniteField;

/// Binary extension field GF_{2^{2^K}} using binary towers arithmetic as explained in Section 2.3 of [DP23b](https://eprint.iacr.org/2023/1784.pdf)
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
    let mut coefficients = [BinaryField::ZERO; 1 << K];
    coefficients[0] = BinaryField::ONE;
    BinaryFieldExtension { coefficients }
  }
}

impl<const K: usize> FiniteField for BinaryFieldExtension<K>
where [(); 1 << K]:
{
  const ONE: Self = Self::ONE;
  const ORDER: usize = 1 << (1 << K);
  // TODO: incorrect
  const PRIMITIVE_ELEMENT: Self = Self::ONE;
  const ZERO: Self = Self::default();

  fn pow(self, power: usize) -> Self {
    let mut result = BinaryFieldExtension::ONE;
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

  fn inverse(&self) -> Option<Self> {
    if *self == Self::ZERO {
      return None;
    }
    Some(self.pow(Self::ORDER - 2))
  }
}

// Function to find a primitive element
// const fn find_primitive_element<const K: usize>() -> BinaryFieldExtension<K>
// where [(); 1 << K]: {
//   let mut candidate = BinaryFieldExtension::<K>::one();
//   let order = BinaryFieldExtension::<K>::ORDER;

//   loop {
//     let mut is_primitive = true;

//     for i in 1..order {
//       if candidate.pow(i) == GF2k::<K>::ONE {
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
//         *coef = BinaryField(1);
//         break;
//       } else {
//         *coef = BinaryField(0);
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
    BinaryFieldExtension::<K>::new(multiply(&self.coefficients, &rhs.coefficients, K))
  }
}

// const fn mul_ext<const K: usize>(lhs: BinaryFieldExtension<K>, rhs: BinaryFieldExtension<K>) ->
// BinaryFieldExtension<K> {

// }

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

  // TODO: recheck
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

pub(super) fn multiply(v1: &[BinaryField], v2: &[BinaryField], k: usize) -> Vec<BinaryField> {
  debug_assert!(v1.len() == v2.len(), "v1 and v2 should be of same size");

  if k == 0 {
    let res = v1[0] * v2[0];
    return vec![res];
  }

  let halflen = v1.len() / 2;
  let quarterlen = halflen / 2;

  let (l1, r1) = v1.split_at(halflen);
  let (l2, r2) = v2.split_at(halflen);

  let l1l2 = multiply(l1, l2, k - 1);
  let r1r2 = multiply(r1, r2, k - 1);

  let z3 = multiply(&add_vec(l1, r1), &add_vec(l2, r2), k - 1);

  let mut k2_val = vec![BinaryField::new(0); 1 << (k - 1)];
  k2_val[quarterlen] = BinaryField::new(1);

  let r1r2_high = multiply(&k2_val, &r1r2, k - 1);
  let mut res_low = add_vec(&l1l2, &r1r2);
  let res_high = add_vec(&z3, &l1l2);
  let res_high = add_vec(&res_high, &r1r2);
  let mut res_high = add_vec(&res_high, &r1r2_high);
  res_low.append(&mut res_high);

  res_low
}

fn add_vec(lhs: &[BinaryField], rhs: &[BinaryField]) -> Vec<BinaryField> {
  lhs.iter().zip(rhs).map(|(a, b)| *a + *b).collect()
}

pub(super) fn num_digits(n: u64) -> usize {
  let r = format!("{:b}", n);
  r.len()
}

pub(super) fn to_bool_vec(mut num: u64) -> Vec<BinaryField> {
  let length = 1 << num_digits((num_digits(num) - 1) as u64);
  let mut result = Vec::new();
  while num > 0 {
    result.push(BinaryField::new(((num & 1) != 0) as u8));
    num >>= 1;
  }
  result.extend(std::iter::repeat(BinaryField::new(0)).take(length - result.len()));
  result
}
