//! Arithmetic operations for multivariate polynomials.
//! The operations are implemented for [`MultiVarPolynomial`] in the monomial basis.
//!
//! Note: Operations are restricted to polynomials with the same degree structure.
//!
//! ## Implementations
//! - [`Add`] for adding two multivariate polynomials.
//! - [`AddAssign`] for adding two multivariate polynomials in place.
//! - [`Sum`] for summing a collection of multivariate polynomials.
//! - [`Sub`] for subtracting two multivariate polynomials.
//! - [`SubAssign`] for subtracting two multivariate polynomials in place.
//! - [`Neg`] for negating a multivariate polynomial.
//! - [`Mul`] for scalar multiplication of a multivariate polynomial.
//! - [`MulAssign`] for scalar multiplication of a multivariate polynomial in place.

use std::{
  iter::Sum,
  ops::{Add, AddAssign, Neg, Sub, SubAssign},
};

use super::*;

impl<F: FiniteField> Add for MultiVarPolynomial<F> {
  type Output = Self;

  /// Implements addition of two multivariate polynomials by adding their coefficients.
  fn add(self, rhs: Self) -> Self::Output {
    assert_eq!(self.degree, rhs.degree, "Polynomials must have the same degree structure");

    let coefficients =
      self.coefficients.iter().zip(rhs.coefficients.iter()).map(|(&a, &b)| a + b).collect();

    Self { degree: self.degree, coefficients }
  }
}

impl<F: FiniteField> AddAssign for MultiVarPolynomial<F> {
  /// Implements in-place addition of two multivariate polynomials by adding their coefficients.
  fn add_assign(&mut self, rhs: Self) {
    assert_eq!(self.degree, rhs.degree, "Polynomials must have the same degree structure");

    for (a, b) in self.coefficients.iter_mut().zip(rhs.coefficients.iter()) {
      *a += *b;
    }
  }
}

impl<F: FiniteField> Sum for MultiVarPolynomial<F> {
  /// Implements summing a collection of multivariate polynomials.
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).expect("Cannot sum an empty iterator of MultiVarPolynomials")
  }
}

impl<F: FiniteField> Sub for MultiVarPolynomial<F> {
  type Output = Self;

  /// Implements subtraction of two multivariate polynomials by subtracting their coefficients.
  fn sub(self, rhs: Self) -> Self::Output {
    assert_eq!(self.degree, rhs.degree, "Polynomials must have the same degree structure");

    let coefficients =
      self.coefficients.iter().zip(rhs.coefficients.iter()).map(|(&a, &b)| a - b).collect();

    Self { degree: self.degree, coefficients }
  }
}

impl<F: FiniteField> SubAssign for MultiVarPolynomial<F> {
  /// Implements in-place subtraction of two multivariate polynomials by subtracting their
  /// coefficients.
  fn sub_assign(&mut self, rhs: Self) {
    assert_eq!(self.degree, rhs.degree, "Polynomials must have the same degree structure");

    for (a, b) in self.coefficients.iter_mut().zip(rhs.coefficients.iter()) {
      *a -= *b;
    }
  }
}

impl<F: FiniteField> Neg for MultiVarPolynomial<F> {
  type Output = Self;

  /// Implements negation of a multivariate polynomial by negating its coefficients.
  fn neg(self) -> Self::Output {
    Self {
      degree:       self.degree,
      coefficients: self.coefficients.into_iter().map(|c| -c).collect(),
    }
  }
}

impl<F: FiniteField> Mul<F> for MultiVarPolynomial<F> {
  type Output = Self;

  /// Implements scalar multiplication of a multivariate polynomial.
  fn mul(self, rhs: F) -> Self::Output { self.scalar_mul(rhs) }
}

impl<F: FiniteField> MulAssign<F> for MultiVarPolynomial<F> {
  /// Implements in-place scalar multiplication of a multivariate polynomial.
  fn mul_assign(&mut self, rhs: F) {
    for coeff in &mut self.coefficients {
      *coeff *= rhs;
    }
  }
}
