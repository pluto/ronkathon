use std::{
  cmp::{Eq, PartialEq},
  ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use super::Finite;

pub trait Ring:
  std::fmt::Debug
  + Default
  + Sized
  + Copy
  + Clone
  + PartialEq
  + Eq
  + Add<Output = Self>
  + AddAssign
  + Sub<Output = Self>
  + SubAssign
  + Mul<Output = Self>
  + MulAssign
  + Neg<Output = Self>
  + 'static {
  const ZERO: Self;
  const ONE: Self;
}

// pub trait FiniteRing: Finite + Ring {
//   const PRIMITIVE_ELEMENT: Self;
// }
