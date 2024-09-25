//! This module contains the implementation of multivariate polynomials in the monomial basis.
//!
//! ## Overview
//! A multivariate polynomial is a mathematical expression that consists of multiple variables and
//! coefficients. The variables are raised to non-negative integer powers and multiplied by the
//! coefficients. For example, the polynomial $f(x,y,z) = 1 + 2x + 3y + 4z + 5xy + 6yz + 7xz + 8xyz$
//! is a multivariate polynomial with three variables.
//!
//! - [`MultiVarPolynomial`] struct represents a multivariate polynomial in the monomial basis.
//! - Includes arithmetic operations such as addition, subtraction, and scalar multiplication in the
//!   [`arithmetic`] module.
//! - Provides methods for evaluation and summing over boolean hypercube.

use super::*;
use crate::algebra::field::FiniteField;

/// A multivariate polynomial of arbitrary degree.
/// The coefficients are stored in a specific order based on the degree vector.
/// The ordering follows a lexicographic pattern on the exponents of the variables,
/// but in reverse order of the variables (from last to first in the degree vector).
/// For a polynomial with variables x, y, z and degrees dx, dy, dz respectively:
///
/// - The first dz+1 coefficients correspond to increasing powers of z (z^0 to z^dz).
/// - The next dz+1 coefficients correspond to y * (increasing powers of z).
/// - This pattern repeats for each power of y up to dy.
/// - Once all combinations of y and z are exhausted, the power of x increases.
///
/// For example, with degrees [1, 1, 1] (for x, y, z respectively), the coefficient order is:
/// [1, z, y, yz, x, xz, xy, xyz]
///
/// The total number of coefficients is (dx+1) * (dy+1) * (dz+1).
///
/// This ordering allows for efficient indexing and evaluation of the polynomial,
/// particularly when iterating over the boolean hypercube or performing other operations.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MultiVarPolynomial<F: FiniteField> {
  /// Vector representing the maximum degree for each variable.
  pub degree:       Vec<usize>,
  /// Coefficients of the polynomial in the monomial basis.
  // The ordering follows a lexicographic pattern on the exponents of the variables,
  /// but in reverse order of the variables (from last to first in the degree vector).
  ///
  /// See comment for [`MultiVarPolynomial`] for more details
  pub coefficients: Vec<F>,
}

/// Generates the cartesian product `(0..l[0]) X (0..l[1]) X  ... X (0..l[n-1])`
///
/// Ordering: the first coordinate is the "most significant" one.
///
/// Example: for input `l = [2,3]`, this outputs `[[0,0], [0,1], [0,2], [1,0], [1,1], [1,2]]`
///
/// This is used internally for polynomial operations.
fn generate_cartesian_product(l: Vec<usize>) -> Vec<Vec<usize>> {
  let mut result = vec![vec![]];

  for element in &l {
    let mut new_result = Vec::new();
    for item in result.iter() {
      for j in 0..*element {
        let mut new_item = item.clone();
        new_item.push(j);
        new_result.push(new_item);
      }
    }
    result = new_result;
  }

  result
}

impl<F: FiniteField> MultiVarPolynomial<F> {
  /// Create a new multivariate polynomial.
  ///
  /// ## Arguments:
  /// - `degree`: A vector of usize representing the maximum degree for each variable.
  /// - `coefficients`: A vector of field elements representing the coefficients of the polynomial.
  ///   The ordering should be the same as the one for the coefficients in the struct. See comments
  ///   for [`MultiVarPolynomial`].
  ///
  /// ## Returns:
  /// - A Result containing the new MultiVarPolynomial or an error message if the number of
  ///   coefficients doesn't match the expected count based on the degree vector.
  pub fn new(degree: Vec<usize>, coefficients: Vec<F>) -> Result<Self, String> {
    // Calculate the expected number of coefficients
    let expected_coeff_count = degree.iter().map(|&d| d + 1).fold(1, Mul::mul);

    // Check if the number of coefficients matches the expected count
    if coefficients.len() != expected_coeff_count {
      return Err(format!(
        "Invalid number of coefficients. Expected {}, but got {}.",
        expected_coeff_count,
        coefficients.len()
      ));
    }

    Ok(Self { degree, coefficients })
  }

  /// Constructs a multivariate polynomial from coordinates and coefficients.
  ///
  /// ## Arguments:
  /// - `coordinates`: A vector of vectors, where each inner vector represents the degrees of a
  ///   term.
  /// - `coefficients`: A vector of coefficients corresponding to the `coordinates` above.
  ///
  /// ## Returns:
  /// - A Result containing the constructed polynomial or an error message.
  ///
  /// Note: This method doesn't handle cases where the same coefficient is filled twice.
  pub fn from_coordinates(
    coordinates: Vec<Vec<usize>>,
    coefficients: Vec<F>,
  ) -> Result<Self, String> {
    if coordinates.len() != coefficients.len() {
      return Err("The number of coordinates must match the number of coefficients".to_string());
    }

    if coordinates.is_empty() {
      return Err("At least one term is required".to_string());
    }

    let num_vars = coordinates[0].len();
    if !coordinates.iter().all(|coord| coord.len() == num_vars) {
      return Err("All coordinates must have the same number of variables".to_string());
    }

    let degree: Vec<usize> =
      (0..num_vars).map(|i| coordinates.iter().map(|coord| coord[i]).max().unwrap_or(0)).collect();

    let total_terms: usize = degree.iter().map(|&d| d + 1).product();
    let mut full_coefficients = vec![F::ZERO; total_terms];

    for (coord, &coeff) in coordinates.iter().zip(coefficients.iter()) {
      let index = coord.iter().enumerate().fold(0, |acc, (i, &d)| {
        acc + d * degree.get(i + 1..).unwrap_or(&[]).iter().map(|&d| d + 1).product::<usize>()
      });
      full_coefficients[index] = coeff;
    }

    Self::new(degree, full_coefficients)
  }

  /// Evaluates the polynomial at a given point.
  ///
  /// ## Arguments:
  /// - `r`: A vector of field elements representing the point at which to evaluate the polynomial.
  ///
  /// ## Returns:
  /// - The result of evaluating the polynomial at the given point.
  pub fn evaluation(&self, r: &[F]) -> F {
    assert_eq!(r.len(), self.num_var());
    let degree_plus_1 = self.degree.iter().map(|x| x + 1).collect();
    let cartesian_prod = generate_cartesian_product(degree_plus_1);
    let mut result = F::ZERO;
    for (cood, coeff) in cartesian_prod.iter().zip(&self.coefficients) {
      let mut eval_term = F::ONE;
      for j in 0..cood.len() {
        let exp = cood[j];
        eval_term *= r[j].pow(exp);
      }
      result += *coeff * eval_term;
    }
    result
  }

  /// Returns the number of variables in the polynomial.
  pub fn num_var(&self) -> usize { self.degree.len() }

  /// Computes the sum of the polynomial over the boolean hypercube.
  ///
  /// ## Returns:
  /// - The sum of the polynomial evaluated at all points in the boolean hypercube.
  pub fn sum_over_bool_hypercube(&self) -> F {
    // let vec_of_2 = (0..self.num_var()).map(|_| 2 as usize).collect();
    let vec_of_2 = vec![2; self.num_var()];
    let bool_hypercube = generate_cartesian_product(vec_of_2);
    let mut sum = F::ZERO;
    for cood in bool_hypercube {
      let cood_f: Vec<F> = cood.iter().map(|&x| F::from(x)).collect();
      sum += self.evaluation(&cood_f);
    }
    sum
  }

  /// Multiplies the polynomial by a scalar.
  ///
  /// ## Arguments:
  /// - `scalar`: The field element to multiply the polynomial by.
  ///
  /// ## Returns:
  /// - A new MultiVarPolynomial that is the result of the scalar multiplication.
  pub fn scalar_mul(&self, scalar: F) -> Self {
    Self {
      degree:       self.degree.clone(),
      coefficients: self.coefficients.iter().map(|&c| c * scalar).collect(),
    }
  }
}

pub mod arithmetic;
#[cfg(test)] mod tests;
