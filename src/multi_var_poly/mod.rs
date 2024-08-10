use super::*;
use crate::algebra::field::FiniteField;

// L is the number of variables
pub struct MultiVarPolynomial<F: FiniteField, const L: usize> {
  degree:       [usize; L],
  coefficients: Vec<F>,
}

fn generate_cartesian_product(n: usize, l: &[usize]) -> Vec<Vec<usize>> {
  let mut result = vec![vec![]];

  for i in 0..n {
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

impl<F: FiniteField, const L: usize> MultiVarPolynomial<F, L> {
  pub fn new(degree: [usize; L], coefficients: Vec<F>) -> Result<Self, String> {
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

  fn evaluation(&self, r: [F; L]) -> F {
    let degree_plus_1 = self.degree.map(|x| x + 1);
    let cartesian_prod = generate_cartesian_product(L, &degree_plus_1);
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
}

#[cfg(test)] mod tests;
