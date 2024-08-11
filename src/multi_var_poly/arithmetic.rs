use std::{
  iter::Sum,
  ops::{Add, AddAssign, Neg, Sub, SubAssign},
};

use super::*;

impl<F: FiniteField> Add for MultiVarPolynomial<F> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    assert_eq!(self.degree, rhs.degree, "Polynomials must have the same degree structure");

    let coefficients =
      self.coefficients.iter().zip(rhs.coefficients.iter()).map(|(&a, &b)| a + b).collect();

    Self { degree: self.degree, coefficients }
  }
}

impl<F: FiniteField> AddAssign for MultiVarPolynomial<F> {
  fn add_assign(&mut self, rhs: Self) {
    assert_eq!(self.degree, rhs.degree, "Polynomials must have the same degree structure");

    for (a, b) in self.coefficients.iter_mut().zip(rhs.coefficients.iter()) {
      *a += *b;
    }
  }
}

impl<F: FiniteField> Sum for MultiVarPolynomial<F> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).expect("Cannot sum an empty iterator of MultiVarPolynomials")
  }
}

impl<F: FiniteField> Sub for MultiVarPolynomial<F> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self::Output {
    assert_eq!(self.degree, rhs.degree, "Polynomials must have the same degree structure");

    let coefficients =
      self.coefficients.iter().zip(rhs.coefficients.iter()).map(|(&a, &b)| a - b).collect();

    Self { degree: self.degree, coefficients }
  }
}

impl<F: FiniteField> SubAssign for MultiVarPolynomial<F> {
  fn sub_assign(&mut self, rhs: Self) {
    assert_eq!(self.degree, rhs.degree, "Polynomials must have the same degree structure");

    for (a, b) in self.coefficients.iter_mut().zip(rhs.coefficients.iter()) {
      *a -= *b;
    }
  }
}

impl<F: FiniteField> Neg for MultiVarPolynomial<F> {
  type Output = Self;

  fn neg(self) -> Self::Output {
    Self {
      degree:       self.degree,
      coefficients: self.coefficients.into_iter().map(|c| -c).collect(),
    }
  }
}

impl<F: FiniteField> Mul<F> for MultiVarPolynomial<F> {
  type Output = Self;

  fn mul(self, rhs: F) -> Self::Output { self.scalar_mul(rhs) }
}

// Implement MulAssign to support *=
impl<F: FiniteField> MulAssign<F> for MultiVarPolynomial<F> {
  fn mul_assign(&mut self, rhs: F) {
    for coeff in &mut self.coefficients {
      *coeff *= rhs;
    }
  }
}
