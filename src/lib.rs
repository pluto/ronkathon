#![feature(const_trait_impl)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![warn(missing_docs)]

pub mod curves;
pub mod field;
pub mod kzg;
pub mod polynomial;
pub mod setup;

use core::{
  fmt::{self, Display, Formatter},
  hash::Hash,
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign},
};

use rand::Rng;
#[cfg(test)] use rstest::{fixture, rstest};

use self::{
  field::{gf_101::GF101, Ext, FiniteField},
  polynomial::{Monomial, Polynomial},
};
