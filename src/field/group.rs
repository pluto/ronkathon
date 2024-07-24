//! Groups $G$ are algebraic structures which are set and has a binary operation $\oplus$ that
//! combines two elements $a, b$ of the set to produce a third element $a\oplus b$ in the set.
//! The operation is said to have following properties:
//! 1. Closure: $a\oplus b=c\in G$
//! 2. Associative: $(a\oplus b)\oplus c = a\oplus(b\oplus c)$
//! 3. Existence of Identity element: $a\oplus 0 = 0\oplus a = a$
//! 4. Existence of inverse element for every element of the set: $a\oplus b=0$
//! 5. Commutativity: Groups which satisfy an additional property: *commutativity* on the set of
//!    elements are known as **Abelian groups**.
//!
//! [`FiniteGroup`] trait is implemented for all finite groups.
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use super::{prime::find_primitive_element, FiniteField, PrimeField};

#[const_trait]
/// Group trait with finite number of elements
pub trait FiniteGroup:
  std::fmt::Debug
  + Sized
  + Add<Output = Self>
  + AddAssign
  + Sub<Output = Self>
  + SubAssign
  + Neg
  + Mul<Self::Scalar, Output = Self>
  + MulAssign<Self::Scalar>
  + Clone
  + Copy
  + Default
  + Eq {
  /// Scalar defined in the group
  type Scalar: FiniteField;
  /// Identity element of group
  const IDENTITY: Self;
  /// total number of elements in group
  const ORDER: usize;
  /// primtive element of group
  const GENERATOR: Self;

  /// operation defined for the group, can be `+` for additive group and `*` for multiplicative
  /// group
  fn operation(a: &Self, b: &Self) -> Self;

  /// Inverse of group element: a ⨁ i = [`FiniteGroup::IDENTITY`]
  fn inverse(&self) -> Self;

  /// Multiplication with the scalar element of the group, i.e. repeatedly applying group
  /// [`FiniteGroup::operation`] `b` number of times.
  fn scalar_mul(&self, scalar: &Self::Scalar) -> Self;
}

/// Additive group on integer $\mathbb{Z}_p$ modulo over prime `P`.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct AdditivePrimeGroup<const P: usize>(usize);

impl<const P: usize> AdditivePrimeGroup<P> {
  /// generates new group element
  pub fn new(val: usize) -> Self { Self(val % Self::ORDER) }
}

impl<const P: usize> FiniteGroup for AdditivePrimeGroup<P> {
  type Scalar = PrimeField<P>;

  const GENERATOR: Self = Self(1);
  const IDENTITY: Self = Self(0);
  const ORDER: usize = P;

  fn operation(a: &Self, b: &Self) -> Self { Self((a.0 + b.0) % Self::ORDER) }

  fn inverse(&self) -> Self { Self(Self::ORDER - self.0) }

  /// naive scalar multiplication
  fn scalar_mul(&self, b: &Self::Scalar) -> Self {
    let mut res = *self;
    for _ in 0..b.value {
      res += *self;
    }
    res
  }
}

impl<const P: usize> Add for AdditivePrimeGroup<P> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output { <Self as FiniteGroup>::operation(&self, &rhs) }
}

impl<const P: usize> AddAssign for AdditivePrimeGroup<P> {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<const P: usize> Neg for AdditivePrimeGroup<P> {
  type Output = Self;

  fn neg(self) -> Self::Output { Self(Self::ORDER - self.0) }
}

impl<const P: usize> Sub for AdditivePrimeGroup<P> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self::Output { self + (-rhs) }
}

impl<const P: usize> SubAssign for AdditivePrimeGroup<P> {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<const P: usize> Mul<PrimeField<P>> for AdditivePrimeGroup<P> {
  type Output = Self;

  fn mul(self, rhs: PrimeField<P>) -> Self::Output {
    <Self as FiniteGroup>::scalar_mul(&self, &rhs)
  }
}

impl<const P: usize> MulAssign<PrimeField<P>> for AdditivePrimeGroup<P> {
  fn mul_assign(&mut self, rhs: PrimeField<P>) { *self = *self * rhs; }
}

/// [`FiniteGroup`] under multiplication implemented as integer, $Z/rZ$ modulo prime `r`.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct MultiplicativePrimeGroup<const P: usize>(usize);

impl<const P: usize> FiniteGroup for MultiplicativePrimeGroup<P> {
  type Scalar = PrimeField<P>;

  const GENERATOR: Self = Self(find_primitive_element::<P>());
  const IDENTITY: Self = Self(1);
  const ORDER: usize = P;

  fn operation(a: &Self, b: &Self) -> Self { Self(a.0 * b.0 % Self::ORDER) }

  fn inverse(&self) -> Self { self.scalar_mul(&Self::Scalar::new(Self::ORDER - 2)) }

  fn scalar_mul(&self, b: &Self::Scalar) -> Self {
    let mut res = Self(1);
    for _ in 0..b.value {
      res = Self::operation(&res, self);
    }
    res
  }
}

impl<const P: usize> Add for MultiplicativePrimeGroup<P> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output { Self::operation(&self, &rhs) }
}

impl<const P: usize> AddAssign for MultiplicativePrimeGroup<P> {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<const P: usize> Neg for MultiplicativePrimeGroup<P> {
  type Output = Self;

  fn neg(self) -> Self::Output { Self::inverse(&self) }
}

impl<const P: usize> Sub for MultiplicativePrimeGroup<P> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self::Output { self + -rhs }
}

impl<const P: usize> SubAssign for MultiplicativePrimeGroup<P> {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<const P: usize> Mul<PrimeField<P>> for MultiplicativePrimeGroup<P> {
  type Output = Self;

  fn mul(self, rhs: PrimeField<P>) -> Self::Output { Self::scalar_mul(&self, &rhs) }
}

impl<const P: usize> MulAssign<PrimeField<P>> for MultiplicativePrimeGroup<P> {
  fn mul_assign(&mut self, rhs: PrimeField<P>) { *self = *self * rhs; }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn add_group_properties() {
    type AddGroup = AdditivePrimeGroup<17>;
    let one = AddGroup::new(1);
    let ident = AddGroup::IDENTITY;

    // commutativity
    assert_eq!(one + ident, ident + one);
    // inverse
    assert_eq!(one + one.inverse(), ident);
    // associativity
    assert_eq!(one + (ident + one), (one + ident) + one);
    // scalar multiplication
    assert_eq!(one * PrimeField::<17>::new(2), one + one);
  }

  #[test]
  fn mul_group_properties() {
    type MulGroup = MultiplicativePrimeGroup<17>;
    type ScalarField = PrimeField<17>;

    let gen = MultiplicativePrimeGroup::<17>::GENERATOR;

    let ident = MulGroup::IDENTITY;

    // commutativity
    assert_eq!(gen + ident, ident + gen);
    // inverse
    assert_eq!(gen + gen.inverse(), ident);
    // associativity
    assert_eq!(gen + (ident + gen), (gen + gen) + ident);
    // scalar multiplication
    assert_eq!(gen * ScalarField::new(2), gen + gen);
  }
}
