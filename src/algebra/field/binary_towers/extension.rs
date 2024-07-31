//! contains implementation of binary extension fields using tower field arithmetic in multilinear basis as defined in [DP23b](https://eprint.iacr.org/2023/1784.pdf)
use std::{
  cmp::Ordering,
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign},
};

use rand::{
  distributions::{Distribution, Standard},
  Rng,
};

use super::{BinaryField, Field, Finite, FiniteField};

/// Binary extension field GF_{2^{2^K}} using binary towers arithmetic as explained in Section 2.3 of [DP23b](https://eprint.iacr.org/2023/1784.pdf)
/// represented as vector of 2^K [`BinaryField`] components in multilinear basis,
/// i.e. an element $b_v = \prod_{i=0}^{k-1}(v_i.X_i+(1-v_i))$ where $v_i$ is in GF(2).
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct BinaryTowers<const K: usize>
where [(); 1 << K]: {
  /// coefficient of field element
  pub coefficients: [BinaryField; 1 << K],
}

impl<const K: usize> BinaryTowers<K>
where [(); 1 << K]:
{
  /// create extension field element from coefficient vector of [`BinaryField`]
  pub const fn new(value: [BinaryField; 1 << K]) -> Self { Self { coefficients: value } }

  const fn one() -> Self {
    let mut coefficients = [BinaryField::ZERO; 1 << K];
    coefficients[0] = BinaryField::ONE;
    BinaryTowers { coefficients }
  }
}

impl<const K: usize> Finite for BinaryTowers<K>
where [(); 1 << K]:
{
  const ORDER: usize = 1 << (1 << K);
}

impl<const K: usize> Field for BinaryTowers<K>
where [(); 1 << K]:
{
  const ONE: Self = Self::one();
  const ZERO: Self = Self::new([BinaryField::ZERO; 1 << K]);

  fn pow(self, power: usize) -> Self {
    let mut result = BinaryTowers::ONE;
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

impl<const K: usize> FiniteField for BinaryTowers<K>
where [(); 1 << K]:
{
  // TODO: incorrect
  const PRIMITIVE_ELEMENT: Self = Self::ONE;
}

impl<const K: usize> Default for BinaryTowers<K>
where [(); 1 << K]:
{
  fn default() -> Self { Self::ZERO }
}

impl<const K: usize> Add for BinaryTowers<K>
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

impl<const K: usize> AddAssign for BinaryTowers<K>
where [(); 1 << K]:
{
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<const K: usize> Sum for BinaryTowers<K>
where [(); 1 << K]:
{
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(Self::default())
  }
}

impl<const K: usize> Sub for BinaryTowers<K>
where [(); 1 << K]:
{
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn sub(self, rhs: Self) -> Self::Output { self + rhs }
}

impl<const K: usize> SubAssign for BinaryTowers<K>
where [(); 1 << K]:
{
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<const K: usize> MulAssign for BinaryTowers<K>
where [(); 1 << K]:
{
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<const K: usize> Product for BinaryTowers<K>
where [(); 1 << K]:
{
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::one())
  }
}

impl<const K: usize, const K2: usize> Mul<BinaryTowers<K2>> for BinaryTowers<K>
where
  [(); 1 << K]:,
  [(); 1 << K2]:,
{
  type Output = Self;

  /// multiplies a [`BinaryTowers`]::<K> with [`BinaryTowers`]::<K2> by efficient
  /// small-by-large field multiplication in binary extension fields. breaks down K into chunks of
  /// `1<<K2` and define K's basis in `K2`.
  ///
  /// **Note**: return self if K < K2.
  #[allow(clippy::suspicious_arithmetic_impl)]
  fn mul(self, rhs: BinaryTowers<K2>) -> Self::Output {
    match K.cmp(&K2) {
      Ordering::Equal => {
        let res = multiply(&self.coefficients, &rhs.coefficients, K).try_into().unwrap_or_else(
          |v: Vec<BinaryField>| panic!("expected vec of len: {}, but found: {}", 1 << K, v.len()),
        );
        BinaryTowers::<K>::new(res)
      },
      Ordering::Less => self,
      Ordering::Greater => {
        let small_values = self
          .coefficients
          .chunks_exact(1 << K2)
          .map(|v| {
            let coefficients: [BinaryField; 1 << K2] =
              v.try_into().expect("expected a vec of size");
            BinaryTowers::<K2>::new(coefficients) * rhs
          })
          .collect::<Vec<BinaryTowers<K2>>>();
        let mut coefficients = [BinaryField::ZERO; 1 << K];
        for (i, value) in small_values.iter().enumerate() {
          let range_start = i * (1 << K2);
          coefficients[range_start..range_start + (1 << K2)]
            .copy_from_slice(&value.coefficients[..]);
        }
        BinaryTowers::<K>::new(coefficients)
      },
    }
  }
}

impl<const K: usize> Neg for BinaryTowers<K>
where [(); 1 << K]:
{
  type Output = Self;

  fn neg(self) -> Self::Output { self }
}

impl<const K: usize> Div for BinaryTowers<K>
where [(); 1 << K]:
{
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().unwrap() }
}

impl<const K: usize> DivAssign for BinaryTowers<K>
where [(); 1 << K]:
{
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl<const K: usize> Rem for BinaryTowers<K>
where [(); 1 << K]:
{
  type Output = Self;

  fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
}

impl<const K: usize> From<usize> for BinaryTowers<K>
where [(); 1 << K]:
{
  fn from(value: usize) -> Self {
    let coefficients =
      to_bool_vec(value as u64, 1 << K).try_into().unwrap_or_else(|v: Vec<BinaryField>| {
        panic!("Expected a Vec of length {} but it was {}", 1 << K, v.len())
      });
    Self { coefficients }
  }
}

impl<const K: usize> From<BinaryTowers<K>> for (BinaryTowers<{ K - 1 }>, BinaryTowers<{ K - 1 }>)
where
  [(); 1 << K]:,
  [(); 1 << { K - 1 }]:,
{
  fn from(value: BinaryTowers<K>) -> Self {
    debug_assert!(K > 1, "K cannot be less than 1");
    let lhs: [BinaryField; 1 << (K - 1)] = value.coefficients[..1 << (K - 1)].try_into().unwrap();
    let rhs: [BinaryField; 1 << (K - 1)] = value.coefficients[1 << (K - 1)..].try_into().unwrap();
    let lhs = BinaryTowers::<{ K - 1 }>::new(lhs);
    let rhs = BinaryTowers::<{ K - 1 }>::new(rhs);
    (lhs, rhs)
  }
}

impl<const K: usize> From<(BinaryTowers<K>, BinaryTowers<K>)> for BinaryTowers<{ K + 1 }>
where
  [(); 1 << K]:,
  [(); 1 << { K + 1 }]:,
{
  fn from(value: (BinaryTowers<{ K }>, BinaryTowers<{ K }>)) -> Self {
    let mut result = [BinaryField::ZERO; 1 << (K + 1)];
    result[..1 << K].copy_from_slice(&value.0.coefficients);
    result[1 << K..].copy_from_slice(&value.1.coefficients);
    BinaryTowers::<{ K + 1 }>::new(result)
  }
}

impl<const K: usize> Distribution<BinaryTowers<K>> for Standard
where [(); 1 << K]:
{
  #[inline]
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> BinaryTowers<K> {
    let num = rng.gen_range(1..1 << (1 << K));
    let coefficients = to_bool_vec(num, 1 << K).try_into().unwrap_or_else(|v: Vec<BinaryField>| {
      panic!("Expected a Vec of length {} but it was {}", 1 << K, v.len())
    });
    BinaryTowers::<K>::new(coefficients)
  }
}

/// Uses karatsuba style multiplication to multiply two elements of field extension.
/// represents a field extension element in 2^K length vector of [`BinaryField`] coefficients to
/// form [`BinaryTowers`]. Elements are broken down into `a = a_1*X_{i-1}+a_0` and reduction
/// rule: `$X_{i}^{2}=X_i*X_{i-1}+1$`
/// - a*a' = (r1*X_{i-1}+l1)(r2*X_{i-1}+l2)
/// - (l1l2) + r1r2*X_{i-1}^2 + (l1r2+l2r1)*X_{i-1}
/// - reduction rule is applied: (l1l2+r1r2) + X_{i-1}(l1r2+l2r1+r1r2*X_{i-2})
/// - r1r2*X_{i-2} is computed separately
/// - by karatsuba multiplication: (l1r2+l2r1) = (l1+l2)*(r1+r2)-(l1l2+r1r2)
pub(super) fn multiply(a: &[BinaryField], b: &[BinaryField], k: usize) -> Vec<BinaryField> {
  debug_assert!(a.len() == b.len(), "v1 and v2 should be of same size");

  // if elements of BinaryField, multiply
  if k == 0 {
    let res = a[0] * b[0];
    return vec![res];
  }

  let halflen = a.len() / 2;
  let quarterlen = halflen / 2;

  // break down into components of X_{i-1}
  let (l1, r1) = a.split_at(halflen);
  let (l2, r2) = b.split_at(halflen);

  // compute l1l2, r1r2
  let l1l2 = multiply(l1, l2, k - 1);
  let r1r2 = multiply(r1, r2, k - 1);

  // (l1+r1)*(l2+r2)
  let temp = multiply(&add_vec(l1, r1), &add_vec(l2, r2), k - 1);

  // r1r2*X_{i-2}
  // X_{i-2}: a+b*x where a, b are vectors of length K/4, with a = 0, b = 1
  let mut x_i_high = vec![BinaryField::Zero; 1 << (k - 1)];
  x_i_high[quarterlen] = BinaryField::ONE;
  let r1r2_high = multiply(&x_i_high, &r1r2, k - 1);

  // res = (l1l2+r1r2) + X_{i-1}(z3-(l1l2+r1r2)-r1r2_high)
  let mut res_low = add_vec(&l1l2, &r1r2);
  let res_high = add_vec(&temp, &res_low);
  let mut res_high = add_vec(&res_high, &r1r2_high);

  // res = res_low + X_{i-1}res_high
  res_low.append(&mut res_high);
  res_low
}

fn add_vec(lhs: &[BinaryField], rhs: &[BinaryField]) -> Vec<BinaryField> {
  lhs.iter().zip(rhs).map(|(a, b)| *a + *b).collect()
}

pub(super) fn to_bool_vec(mut num: u64, length: usize) -> Vec<BinaryField> {
  let mut result = Vec::new();
  while num > 0 {
    result.push(match num & 1 {
      0 => BinaryField::Zero,
      _ => BinaryField::One,
    });
    num >>= 1;
  }
  result.extend(std::iter::repeat(BinaryField::Zero).take(length - result.len()));
  result
}
