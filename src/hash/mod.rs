//! Contains implementation of various hash functions

use crate::field::FiniteField;
pub mod poseidon;

/// Sponge trait defining absorb and squeeze behavior of sponge based hash function.
pub trait Sponge<F: FiniteField> {
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
