//! # ronkathon
//! This crate is a library intended for educational purposes. It provides implementations of
//! various cryptographic primitives and protocols, such as polynomial commitments, zero-knowledge
//! proofs, and elliptic curve operations. The library is designed to be simple and easy to
//! understand, with a focus on clarity and correctness rather than performance.
//!
//! ## Features
//! - Finite fields: Implementations of finite fields and extension fields, including arithmetic
//!   operations and field elements.
//! - Polynomials: Implementations of polynomials in various bases, with support for arithmetic
//!   operations such as addition, multiplication, and division.
//! - Elliptic curves: Implementations of elliptic curves over finite fields, with support for
//!   operations such as point addition, scalar multiplication, and pairing operations.
//! - Compiler: Simple DSL to write circuits which can be compiled to polynomials used in PLONK.

#![allow(incomplete_features)]
#![feature(effects)]
#![feature(const_trait_impl)]
#![feature(const_mut_refs)]
#![feature(const_for)]
#![feature(const_option)]
#![feature(generic_const_exprs)]
#![feature(specialization)]
#![feature(test)]
#![warn(missing_docs)]

pub mod algebra;
pub mod codes;
pub mod compiler;
pub mod curve;
pub mod diffie_hellman;
pub mod dsa;
pub mod encryption;
pub mod hashes;
pub mod hmac;
pub mod kzg;
pub mod multi_var_poly;
pub mod polynomial;
pub mod shamir;
pub mod sumcheck;
pub mod tree;

use core::{
  fmt::{self, Display, Formatter},
  hash::Hash,
  iter::Sum,
  ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Rem, Sub, SubAssign},
};

use rand::{
  distributions::{Distribution, Standard},
  Rng,
};
#[cfg(test)] use rstest::{fixture, rstest};

use self::{
  algebra::field::{
    extension::{GaloisField, PlutoBaseFieldExtension},
    prime::{PlutoBaseField, PlutoPrime, PlutoScalarField, PrimeField},
    Field,
  },
  curve::{
    pluto_curve::{PlutoBaseCurve, PlutoExtendedCurve},
    AffinePoint,
  },
  polynomial::{Monomial, Polynomial},
};
