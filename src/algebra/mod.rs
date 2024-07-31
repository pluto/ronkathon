#![doc = include_str!("./README.md")]
//! Defines algebraic types:
//! - [`group::Group`]: Group
//! - [`field::Field`]: Field
pub mod field;
pub mod group;

#[const_trait]
/// Trait defining order of algebraic structure
pub trait Finite {
  /// total number of elements
  const ORDER: usize;
}
