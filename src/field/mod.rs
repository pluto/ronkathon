use std::{
  hash::Hash,
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign},
};

pub mod gf_101;
pub mod gf_101_2;

/// A field is a set of elements on which addition, subtraction, multiplication, and division are
/// defined.
///
/// We restrict to finite fields, which are fields with a finite number of elements.
pub trait FiniteField:
  std::fmt::Debug
  + Default
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
  type Storage: From<u32>
    + Into<u32>
    + Into<u64>
    + Copy
    + std::fmt::Debug
    + Sub<Output = Self::Storage>
    + Div<Output = Self::Storage>
    + Rem<Output = Self::Storage>
    + Mul<Output = Self::Storage>
    + Eq;
  const ORDER: Self::Storage;
  const ZERO: Self;
  const ONE: Self;
  const TWO: Self;
  const NEG_ONE: Self;

  fn inverse(&self) -> Option<Self>;
  fn from_canonical_u32(n: u32) -> Self;
  fn generator() -> Self;
  fn double(&self) -> Self { self.clone() + self.clone() }
  fn square(&self) -> Self { self.clone() * self.clone() }

  fn pow(&self, power: Self::Storage) -> Self {
    let mut current = *self;
    let power: u64 = power.into();
    let mut product = Self::ONE;

    for j in 0..(64 - power.leading_zeros()) as usize {
      if (power >> j & 1) != 0 {
        product *= current;
      }
      current = current * current;
    }
    product
  }

  // In any field of prime order F_p:
  // - There exists an additive group.
  // - There exists a multiplicative subgroup generated by a primitive element 'a'.
  //
  // According to the Sylow theorems (https://en.wikipedia.org/wiki/Sylow_theorems):
  // A non-trivial multiplicative subgroup of prime order 'q' exists if and only if
  // 'p - 1' is divisible by 'q'.
  // The primitive q-th root of unity 'w' is defined as: w = a^((p - 1) / q),
  // and the roots of unity are generated by 'w', such that {w^i | i in [0, q - 1]}.
  fn primitive_root_of_unity(n: Self::Storage) -> Self {
    let p_minus_one = Self::ORDER - Self::Storage::from(1);
    assert!(p_minus_one % n == 0.into(), "n must divide p - 1");
    let pow = p_minus_one / n;
    Self::generator().pow(pow)
  }
}

#[const_trait]
pub trait ExtensionField<Base: FiniteField>:
  FiniteField
  + From<Base>
  + Add<Base, Output = Self>
  + AddAssign<Base>
  + Sub<Base, Output = Self>
  + SubAssign<Base>
  + Mul<Base, Output = Self>
  + MulAssign<Base> {
  const D: usize;
  fn irreducible() -> Base;
  fn from_base(b: Base) -> Self;
}
