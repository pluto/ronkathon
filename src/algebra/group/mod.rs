#![doc = include_str!("./README.md")]
pub mod prime;

use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use super::Finite;

#[const_trait]
/// Group trait defined by a binary operation, identity element and inverse.
pub trait Group:
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
  type Scalar;
  /// Identity element of group
  const IDENTITY: Self;

  /// order of group element
  fn order(&self) -> usize;

  /// operation defined for the group, can be `+` for additive group and `·` for multiplicative
  /// group
  fn operation(a: &Self, rhs: &Self) -> Self;

  /// Inverse of group element: a·i = [`FiniteGroup::IDENTITY`]
  fn inverse(&self) -> Option<Self>;

  /// Multiplication with the scalar element of the group, i.e. repeatedly applying group
  /// [`FiniteGroup::operation`] `scalar` number of times.
  fn scalar_mul(&self, scalar: Self::Scalar) -> Self;
}

#[const_trait]
/// Group trait with finite number of elements
pub trait FiniteGroup: Finite + Group {}

/// Defines a group with commutative operation: `a·b=b·a`
pub trait AbelianGroup: Group {
  /// Returns whether the group is an abelian group
  fn is_abelian(a: &Self, b: &Self) -> bool { Self::operation(a, b) == Self::operation(b, a) }
}

#[const_trait]
/// Finite cyclic group trait defined by a generator element and order of the group
pub trait FiniteCyclicGroup: FiniteGroup + AbelianGroup {
  /// primtive element of group
  const GENERATOR: Self;
}
