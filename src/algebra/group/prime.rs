//! Defines a multiplicative group under multiplication modulo prime `r`.
use super::*;
use crate::{
  algebra::field::prime::find_primitive_element,
  encryption::asymmetric::rsa::{gcd, is_prime},
};

/// [`FiniteGroup`] under multiplication implemented as integer, $(Z/nZ)*$ modulo any prime power
/// number `n=p^k`.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct MultiplicativePrimeGroup<const P: usize, const K: usize>(usize);
impl<const P: usize, const K: usize> MultiplicativePrimeGroup<P, K> {
  #[allow(dead_code)]
  const IS_PRIME: () = assert!(is_prime(P));

  /// create new value in group `Z/nZ`
  pub fn new(value: usize) -> Self { Self(value % (P ^ K)) }
}

impl<const P: usize, const K: usize> Finite for MultiplicativePrimeGroup<P, K> {
  /// P^K - P^{K-1}
  const ORDER: usize = (P ^ K) - (P ^ (K - 1));
}

impl<const P: usize, const K: usize> Group for MultiplicativePrimeGroup<P, K> {
  type Scalar = usize;

  const IDENTITY: Self = Self(1);

  fn op(&self, rhs: &Self) -> Self { Self(self.0 * rhs.0 % (P ^ K)) }

  fn inverse(&self) -> Option<Self> {
    if gcd(self.0 as u64, P as u64) != 1 {
      return None;
    }
    Some(self.scalar_mul(Self::ORDER - 1))
  }

  fn scalar_mul(&self, b: Self::Scalar) -> Self {
    let mut res = Self(1);
    for _ in 0..b {
      res = Self::op(&res, self);
    }
    res
  }
}

impl<const P: usize, const K: usize> FiniteGroup for MultiplicativePrimeGroup<P, K> {
  fn order(&self) -> usize { Self::ORDER }
}

impl<const P: usize, const K: usize> AbelianGroup for MultiplicativePrimeGroup<P, K> {}

impl<const P: usize, const K: usize> FiniteCyclicGroup for MultiplicativePrimeGroup<P, K> {
  const GENERATOR: Self = Self(find_primitive_element::<P>());
}

impl<const P: usize, const K: usize> Add for MultiplicativePrimeGroup<P, K> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output { Self::op(&self, &rhs) }
}

impl<const P: usize, const K: usize> AddAssign for MultiplicativePrimeGroup<P, K> {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<const P: usize, const K: usize> Neg for MultiplicativePrimeGroup<P, K> {
  type Output = Self;

  fn neg(self) -> Self::Output { Self::inverse(&self).expect("inverse does not exist") }
}

impl<const P: usize, const K: usize> Sub for MultiplicativePrimeGroup<P, K> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self::Output { self + -rhs }
}

impl<const P: usize, const K: usize> SubAssign for MultiplicativePrimeGroup<P, K> {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<const P: usize, const K: usize> Mul<usize> for MultiplicativePrimeGroup<P, K> {
  type Output = Self;

  fn mul(self, rhs: usize) -> Self::Output { Self::scalar_mul(&self, rhs) }
}

impl<const P: usize, const K: usize> MulAssign<usize> for MultiplicativePrimeGroup<P, K> {
  fn mul_assign(&mut self, rhs: usize) { *self = *self * rhs; }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn mul_group_properties() {
    type MulGroup = MultiplicativePrimeGroup<5, 2>;

    let gen = MultiplicativePrimeGroup::<5, 2>::GENERATOR;

    let ident = MulGroup::IDENTITY;

    println!("{:?}, {:?}, {}", gen, gen.inverse().unwrap(), MulGroup::ORDER);
    // commutativity
    assert_eq!(gen + ident, ident + gen);
    // inverse
    assert_eq!(gen + gen.inverse().unwrap(), ident);
    // associativity
    assert_eq!(gen + (ident + gen), (gen + gen) + ident);
    // scalar multiplication
    assert_eq!(gen * 2, gen + gen);
    // order
    assert_eq!(gen.order(), MulGroup::ORDER);
  }
}
