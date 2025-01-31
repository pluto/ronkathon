//! Contains a simple DSL for writing circuits that can compile to plonk's polynomials that are used
//! in PLONK.
//!
//! ## DSL
//!
//! let's take an example to compute `x^3 + x + 5`:
//! ### Example
//! ```ignore
//! x public
//! x2 <== x * x
//! out <== x2 * x + 5
//! ```
//!
//! Each line of DSL is a separate constraint. It's parsed and converted to corresponding
//! `WireValues`, i.e. variables and coefficients. Vanilla PLONK supports fan-in 2 arithmetic (add
//! and mul) gates, so each constraint can only support a maximum of 1 output and 2 input variables.
//!
//! Note: Read [`parser`] for DSL rules.
//!
//! ## Program
//!
//! Converts `WireValues` to required polynomials in PLONK, i.e.
//! - Preprocessed polynomials:
//!     - selector polynomials: `[QM,QR,QM,QO,QC]`
//!     - permutation helpers: `[S1,S2,S3]`
//! - public inputs
//! - witness: `[a,b,c]`
#![doc = include_str!("./README.md")]
mod errors;
pub mod parser;
pub mod program;
mod utils;
