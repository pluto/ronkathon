//! # ronkathon
//! This crate is a library intended for educational purposes. It provides implementations of
//! various cryptographic primitives and protocols, such as polynomial commitments, zero-knowledge
//! proofs, and elliptic curve operations. The library is designed to be simple and easy to
//! understand, with a focus on clarity and correctness rather than performance.
//!
//! ## Features
//! - Finite fields: Implementations of finite fields and extension fields, including arithmetic
//!  operations and field elements.
//! - Polynomials: Implementations of polynomials in various bases, with support for arithmetic
//! operations such as addition, multiplication, and division.
//! - Elliptic curves: Implementations of elliptic curves over finite fields, with support for
//! operations such as point addition, scalar multiplication, and pairing operations.

#![feature(const_trait_impl)]
#![allow(incomplete_features)]
#![feature(effects)]
#![feature(const_mut_refs)]
#![feature(const_for)]
#![feature(const_option)]
#![feature(generic_const_exprs)]
#![warn(missing_docs)]

pub mod curve;
pub mod field;
pub mod kzg;
pub mod polynomial;

use core::{
  fmt::{self, Display, Formatter},
  hash::Hash,
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign},
};

use rand::{
  distributions::{Distribution, Standard},
  Rng,
};
#[cfg(test)] use rstest::{fixture, rstest};

use self::{
  curve::{
    pluto_curve::{PlutoBaseCurve, PlutoExtendedCurve},
    AffinePoint,
  },
  field::{
    extension::{GaloisField, PlutoBaseFieldExtension},
    prime::{PlutoBaseField, PlutoPrime, PrimeField},
    FiniteField,
  },
  polynomial::{Monomial, Polynomial},
};
