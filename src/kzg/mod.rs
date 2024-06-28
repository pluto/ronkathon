//! KZG implementation for polynomial commitments
#![doc = include_str!("./README.md")]
#[cfg(test)] mod tests;

pub mod setup;
pub use setup::*;

use super::*;
