use std::{
  hash::Hash,
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign},
};

pub mod gf_101;

/// A field is a set of elements on which addition, subtraction, multiplication, and division are
/// defined.
///
/// We restrict to finite fields, which are fields with a finite number of elements.
pub trait FiniteField:
  std::fmt::Debug
  + Sized
  + Copy
  + Clone
  + PartialEq
  + Eq
  + Add<Output = Self>
  + AddAssign
  + Sum
  + Sub<Output = Self>
  + SubAssign
  + Mul<Output = Self>
  + MulAssign
  + Product
  + Div<Output = Self>
  + DivAssign
  + Neg<Output = Self>
  + Rem<Output = Self>
  + Hash
  + 'static {
  type Storage: From<u32>;
  const PRIME: Self::Storage;
  fn zero() -> Self;
  fn one() -> Self;
  fn two() -> Self;
  fn neg_one() -> Self;
  fn inverse(&self) -> Option<Self>;
  fn exp(&self, power: Self::Storage) -> Self;
  fn generator() -> Self;
  fn primitive_root_of_unity(n: Self::Storage) -> Self;
}
