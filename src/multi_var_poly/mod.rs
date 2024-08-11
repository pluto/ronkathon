use super::*;
use crate::algebra::field::FiniteField;

// L is the number of variables
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MultiVarPolynomial<F: FiniteField> {
  pub degree:       Vec<usize>,
  pub coefficients: Vec<F>,
}

// generates the cartesian product (0..l[0]) X (0..l[1]) X  ... X (0..l[n-1])
fn generate_cartesian_product(l: Vec<usize>) -> Vec<Vec<usize>> {
  let mut result = vec![vec![]];

  for i in 0..l.len() {
    let mut new_result = Vec::new();
    for item in result.iter() {
      for j in 0..l[i] {
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
  /// # Arguments
  /// * `coordinates` - A vector of vectors, where each inner vector represents the degrees of a
  ///   term.
  /// * `coefficients` - A vector of coefficients corresponding to each term.
  ///
  /// # Returns
  /// * `Result<Self, String>` - The constructed polynomial or an error message.
  ///
  /// Doesn't take into account cases where you try to fill the same coefficient twice
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

    // println!("degree = {:?}", degree);

    for (coord, &coeff) in coordinates.iter().zip(coefficients.iter()) {
      let index = coord.iter().enumerate().fold(0, |acc, (i, &d)| {
        acc + d * degree.get(i + 1..).unwrap_or(&[]).iter().map(|&d| d + 1).product::<usize>()
      });
      // println!("Accessing index={}", index);
      // println!("for coord={:?}", coord);
      full_coefficients[index] = coeff;
    }

    Self::new(degree, full_coefficients)
  }

  pub fn evaluation(&self, r: &Vec<F>) -> F {
    assert_eq!(r.len(), self.num_var());
    let degree_plus_1 = self.degree.iter().map(|x| x + 1).collect();
    let cartesian_prod = generate_cartesian_product(degree_plus_1);
    let mut result = F::ZERO;
    for i in 0..cartesian_prod.len() {
      let cood = &cartesian_prod[i];
      let coeff = self.coefficients[i].clone();
      let mut eval_term = F::ONE;
      for j in 0..cood.len() {
        let exp = cood[j];
        eval_term = eval_term * (r[j].pow(exp));
      }
      result += coeff * eval_term;
    }
    return result;
  }

  pub fn num_var(&self) -> usize { self.degree.len() }

  pub fn sum_over_bool_hypercube(&self) -> F {
    // let vec_of_2 = (0..self.num_var()).map(|_| 2 as usize).collect();
    let vec_of_2 = vec![2; self.num_var()];
    let bool_hypercube = generate_cartesian_product(vec_of_2);
    let mut sum = F::ZERO;
    for cood in bool_hypercube {
      let cood_f: Vec<F> = cood.iter().map(|&x| F::from(x)).collect();
      sum += self.evaluation(&cood_f);
    }
    return sum;
  }

  pub fn scalar_mul(&self, scalar: F) -> Self {
    Self {
      degree:       self.degree.clone(),
      coefficients: self.coefficients.iter().map(|&c| c * scalar).collect(),
    }
  }
}

pub mod arithmetic;
#[cfg(test)] mod tests;
