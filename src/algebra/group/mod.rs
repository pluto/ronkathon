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
#![doc = include_str!("./README.md")]
pub mod group;

use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

#[const_trait]
/// Group trait defined by a binary operation and identity element.
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

  /// operation defined for the group, can be `+` for additive group and `*` for multiplicative
  /// group
  fn operation(a: &Self, b: &Self) -> Self;

  /// Inverse of group element: a ⨁ i = [`FiniteGroup::IDENTITY`]
  fn inverse(&self) -> Self;

  /// Multiplication with the scalar element of the group, i.e. repeatedly applying group
  /// [`FiniteGroup::operation`] `scalar` number of times.
  fn scalar_mul(&self, scalar: &Self::Scalar) -> Self;
}

/// Finite group trait with finite number of elements
pub trait FiniteGroup: Group {
  /// total number of elements in group
  const ORDER: usize;
}

/// Finite cyclic group trait defined by a generator element and order of the group
pub trait FiniteCyclicGroup: FiniteGroup {
  /// primtive element of group
  const GENERATOR: Self;
}
