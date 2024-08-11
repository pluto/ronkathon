//! # Random Number Generation and Random Oracle Functionality
//!
//! This module provides traits and utilities for random number generation and
//! random oracle functionality, which are essential for various cryptographic
//! operations and protocols.
//!
//! ## Key Components
//!
//! - `Random`: A trait for types that can be randomly generated.
//! - `RandomOracle`: A trait for types that can be generated using a random oracle approach.
//!
//! These traits allow for flexible and secure generation of random instances
//! for implementing types, supporting both standard random generation and
//! more complex random oracle-based generation.
//!
//! The module is designed to work seamlessly with the `rand` crate's `Rng` trait,
//! providing a consistent interface for random number generation across the library.

use rand::Rng;

/// A trait for types that can be randomly generated.
///
/// Types implementing this trait can create random instances of themselves
/// using a provided random number generator.
pub trait Random {
  /// Generates a random instance of the implementing type.
  ///
  /// # Arguments
  ///
  /// * `rng` - A mutable reference to a random number generator.
  ///
  /// # Returns
  ///
  /// A randomly generated instance of the implementing type.
  fn random<R: Rng + ?Sized>(rng: &mut R) -> Self;
}

/// A trait for types that can be generated using a random oracle.
///
/// Types implementing this trait can create instances of themselves
/// using a provided random number generator and an input byte slice,
/// simulating a random oracle functionality.
pub trait RandomOracle: Random {
  /// Generates an instance of the implementing type using a random oracle approach.
  ///
  /// This method takes both a random number generator and an input byte slice,
  /// allowing for deterministic yet unpredictable output based on the input.
  ///
  /// # Arguments
  ///
  /// * `rng` - A mutable reference to a random number generator.
  /// * `input` - A byte slice used as input to the random oracle.
  ///
  /// # Returns
  ///
  /// An instance of the implementing type, generated using the random oracle approach.
  fn random_oracle<R: Rng + ?Sized>(rng: &mut R, input: &[u8]) -> Self;
}
