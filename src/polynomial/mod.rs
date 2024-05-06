use std::collections::HashSet;

use super::*;
use crate::field::FiniteField;

pub mod arithmetic;

// https://people.inf.ethz.ch/gander/papers/changing.pdf

/// A polynomial of degree N-1 which is generic over the basis and the field.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Polynomial<B: Basis, F: FiniteField> {
  pub coefficients: Vec<F>,
  pub basis:        B,
}

// Type state patern for polynomial bases:
pub trait Basis {
  type Data;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Monomial;
impl Basis for Monomial {
  type Data = ();
}

// https://en.wikipedia.org/wiki/Lagrange_polynomial
pub struct Lagrange<F: FiniteField> {
  pub nodes: Vec<F>,
}

impl<F: FiniteField> Basis for Lagrange<F> {
  type Data = Self;
}

/// A polynomial in monomial basis
impl<F: FiniteField> Polynomial<Monomial, F> {
  pub fn new(coefficients: Vec<F>) -> Self {
    // TODO: This check here may be unecessary as we just need this if we do the conversion to
    // Lagrange basis.
    // // Check that the polynomial degree divides the field order so that there are roots of unity.
    // assert_eq!(
    //   (F::ORDER - F::Storage::from(1_u32)) % F::Storage::from(N as u32),
    //   F::Storage::from(0)
    // );
    assert_ne!(*coefficients.last().unwrap(), F::zero(), "Leading coefficient must be non-zero");
    Self { coefficients, basis: Monomial }
  }

  /// Convert a polynomial from monomial to Lagrange basis using the Barycentric form
  pub fn to_lagrange(&self) -> Polynomial<Lagrange<F>, F> {
    // Get the `N-1`th roots of unity for the field and this degree of polynomial.
    let n = self.coefficients.len();
    let primitive_root = F::primitive_root_of_unity(F::Storage::from(n as u32));

    // Evaluate the polynomial at the roots of unity to get the coefficients of the Lagrange basis
    let mut coeffs = vec![F::zero(); n];
    for j in 0..self.coefficients.len() {
      coeffs[j] = self.evaluate(primitive_root.pow(F::Storage::from(j as u32)));
    }
    Polynomial::<Lagrange<F>, F>::new(coeffs)
  }

  /// Evaluate the polynomial at field element x
  pub fn evaluate(&self, x: F) -> F {
    let mut result = F::zero();
    for (i, c) in self.coefficients.iter().enumerate() {
      result += *c * x.pow(F::Storage::from(i as u32));
    }
    result
  }

  pub fn degree(&self) -> usize { self.coefficients.len() - 1 }

  pub fn leading_coefficient(&self) -> F { *self.coefficients.last().unwrap() }

  pub fn pow_mult(&self, coeff: F, pow: usize) -> Polynomial<Monomial, F> {
    let mut coefficients = vec![F::zero(); self.coefficients.len() + pow];
    self.coefficients.iter().enumerate().for_each(|(i, c)| {
      coefficients[i + pow] = *c * coeff;
    });
    Polynomial::<Monomial, F>::new(coefficients)
  }
}

/// A polynomial in Lagrange basis
impl<F: FiniteField> Polynomial<Lagrange<F>, F> {
  pub fn new(coefficients: Vec<F>) -> Self {
    // Check that the polynomial degree divides the field order so that there are roots of unity.
    let n = coefficients.len();
    assert_eq!(
      (F::ORDER - F::Storage::from(1_u32)) % F::Storage::from(n as u32),
      F::Storage::from(0)
    );
    let primitive_root = F::primitive_root_of_unity(F::Storage::from(n as u32));
    let nodes: Vec<F> = (0..n).map(|i| primitive_root.pow(F::Storage::from(i as u32))).collect();

    Self { coefficients, basis: Lagrange { nodes } }
  }

  pub fn to_monomial(&self) -> Polynomial<Monomial, F> {
    // This is the inverse of the conversion from monomial to Lagrange basis
    // This uses something called the Vandermonde matrix which is defined as:
    //
    //     / 1 | x_0 | x_0^2 | x_0^3 | ... | x_0^(N-1) \
    //     | 1 | x_1 | x_1^2 | x_1^3 | ... | x_1^(N-1) |
    //     | 1 | x_2 | x_2^2 | x_2^3 | ... | x_2^(N-1) |
    // v = | . |  .  |   .   |   .   | ... |    .      |
    //     | . |  .  |   .   |   .   | ... |    .      |
    //     | . |  .  |   .   |   .   | ... |    .      |
    //     \ 1 | x_N | x_N^2 | x_N^3 | ... | x_N^(N-1) /
    //
    // where x_i are the nodes of the Lagrange basis
    //
    // Then the monomial basis m is given V^T * l = m, where l is the Lagrange basis
    // because we know the monomial basis we need to compute to monomial coefficients a_m = V^{-1} *
    // a_l where a_l are the coefficients of the Lagrange basis

    // It also is the case that the the columns of the inverse matrix are the coefficients of the
    // Lagrange polynomial basis TODO Finish this.
    // let nodes = self.basis.nodes;
    // let mut evaluations = [F::zero(); N];

    // // Evaluate the polynomial at N distinct points
    // for i in 0..N {
    //     let x = F::primitive_root().exp_u64(i as u64);
    //     evaluations[i] = self.evaluate(x);
    // }

    // Polynomial::<N, Monomial, F>::new(evaluations)
    todo!("Finish this after we get the roots of unity from other PRs")
  }

  /// Evaluate the polynomial at field element x
  pub fn evaluate(&self, x: F) -> F {
    let n = self.coefficients.len();
    let mut weights = vec![F::one(); n];
    for j in 0..n {
      for m in 0..n {
        if j != m {
          weights[j] *= F::one().div(self.basis.nodes[j] - self.basis.nodes[m]);
        }
      }
    }
    // l(x) = \Sigmm_{m}(x-x_m)
    let l = move |x: F| {
      let mut val = F::one();
      for i in 0..n {
        val *= x - self.basis.nodes[i];
      }
      val
    };

    // L(x) = l(x) * \Sigma_{j=0}^{k}  (w_j / (x - x_j)) y_j
    let mut val = F::zero();
    for j in 0..n {
      // check if we are dividing by zero
      if self.basis.nodes[j] == x {
        return self.coefficients[j];
      }
      val += self.coefficients[j] * weights[j] / (x - self.basis.nodes[j]);
    }
    l(x) * val
  }
}
mod test {
  use super::*;
  use crate::field::gf_101::GF101;

  fn deg_three_poly() -> Polynomial<Monomial, GF101> {
    // Coefficients of the polynomial 1 + 2x + 3x^2 + 4x^3
    let a = GF101::new(1);
    let b = GF101::new(2);
    let c = GF101::new(3);
    let d = GF101::new(4);
    Polynomial::<Monomial, GF101>::new(vec![a, b, c, d])
  }

  #[test]
  fn evaluation() {
    // Should get: 1 + 2*(2) + 3*(2)^2 + 4*(2)^3 = 49
    let y = deg_three_poly().evaluate(GF101::new(2));
    let r = GF101::new(49);
    assert_eq!(y, r);
  }

  #[test]
  fn evaluation_with_zero() {
    // Coefficients of the polynomial 1 + 3x^2
    let a = GF101::new(1);
    let b = GF101::new(0);
    let c = GF101::new(3);
    let polynomial = Polynomial::<Monomial, GF101>::new(vec![a, b, c]);
    let y = polynomial.evaluate(GF101::new(0));

    // Should get: 1 + 3(0)^2 = 1
    let r = GF101::new(1);
    assert_eq!(y, r);
  }

  #[test]
  fn lagrange_evaluation() {
    // Convert to Lagrange basis using roots of unity
    let lagrange = deg_three_poly().to_lagrange();

    // Should get: 1 + 2*(2) + 3*(2)^2 + 4*(2)^2= 49
    let r = lagrange.evaluate(GF101::new(2));
    assert_eq!(r, GF101::new(49));
  }

  #[test]
  #[should_panic]
  fn no_roots_of_unity() {
    // Coefficients of the polynomial 1 + 2x
    let a = GF101::new(1);
    let b = GF101::new(2);
    let c = GF101::new(3);
    let polynomial = Polynomial::<Monomial, GF101>::new(vec![a, b, c]);
    polynomial.to_lagrange();
  }

  #[test]
  fn check_coefficients() {
    assert_eq!(deg_three_poly().coefficients, [
      GF101::new(1),
      GF101::new(2),
      GF101::new(3),
      GF101::new(4)
    ]);

    assert_eq!(deg_three_poly().to_lagrange().coefficients, [
      GF101::new(10),
      GF101::new(79),
      GF101::new(99),
      GF101::new(18)
    ]);
  }

  #[test]
  fn degree() {
    assert_eq!(deg_three_poly().degree(), 3);
  }

  #[test]
  fn leading_coefficient() {
    assert_eq!(deg_three_poly().leading_coefficient(), GF101::new(4));
  }

  #[test]
  fn pow_mult() {
    let poly = deg_three_poly();
    let pow_mult = poly.pow_mult(GF101::new(5), 2);
    assert_eq!(pow_mult.coefficients, [
      GF101::new(0),
      GF101::new(0),
      GF101::new(5),
      GF101::new(10),
      GF101::new(15),
      GF101::new(20)
    ]);
  }
}
