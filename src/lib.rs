#![feature(const_trait_impl)]

pub mod curves;
pub mod field;
pub mod kzg;
pub mod polynomial;

use core::{
  fmt::{self, Display, Formatter},
  hash::Hash,
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign},
};

use rand::Rng;
#[cfg(test)] use rstest::{fixture, rstest};

use self::field::{gf_101::GF101, FiniteField};
