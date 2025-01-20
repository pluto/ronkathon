//! Hashing algorithms
//!
//! This module contains implementations of various hashing algorithms.
//! Currently, the only supported algorithm is SHA-256.
#![doc = include_str!("./README.md")]
pub mod sha;
use crate::Field;
pub mod constants;
pub mod ghash;
pub mod poseidon;

/// Sponge trait defining absorb and squeeze behavior of sponge based hash function.
pub trait Sponge<F: Field> {
  /// apply round function of hash to the sponge state
  fn permute(&mut self);
  /// absorb takes arbitrary number of elements and continue to apply inner permutation on the
  /// elements
  /// ## Arguments
  /// * `elements`: new finite field elements to be absorbed into the sponge
  fn absorb(&mut self, elements: &[F]) -> Result<(), &str>;
  /// squeeze hashed elements out of the sponge
  /// ## Arguments
  /// * `n`: number of elements to be squeezed
  /// ## Output
  /// `elements`: squeezed elements of size `n`
  fn squeeze(&mut self, n: usize) -> Result<Vec<F>, &str>;
}
