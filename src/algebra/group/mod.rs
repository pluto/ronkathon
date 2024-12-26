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

  /// operation defined for the group, can be `+` for additive group and `·` for multiplicative
  /// group
  fn op(&self, rhs: &Self) -> Self;

  /// Inverse of group element: a·i = [`FiniteGroup::IDENTITY`]
  fn inverse(&self) -> Option<Self>;

  /// Multiplication with the scalar element of the group, i.e. repeatedly applying group
  /// [`FiniteGroup::operation`] `scalar` number of times.
  fn scalar_mul(&self, scalar: Self::Scalar) -> Self;
}

/// Group trait with finite number of elements
pub trait FiniteGroup: Finite + Group {
  /// order of group element, i.e. order of finite cyclic subgroup that the element belongs to
  fn order(&self) -> usize {
    let mut order = 1;
    let mut elem = *self;
    for _ in 0..Self::ORDER {
      // check if elem is the identity
      if elem == Self::IDENTITY {
        return order;
      }
      // apply operation and increment order
      elem = Self::op(&elem, self);
      order += 1;
    }
    order
  }
}

/// Defines a group with commutative operation: `a·b=b·a`
pub trait AbelianGroup: Group {
  /// Returns whether the group is an abelian group
  fn is_abelian(a: &Self, b: &Self) { assert!(Self::op(a, b) == Self::op(b, a)) }
}

#[const_trait]
/// Finite cyclic group trait defined by a generator element and order of the group
pub trait FiniteCyclicGroup: FiniteGroup + AbelianGroup {
  /// primitive element of group
  const GENERATOR: Self;
}
