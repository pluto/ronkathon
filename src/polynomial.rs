use std::{collections::HashSet, ops::Div};

use crate::field::FiniteField;

// https://people.inf.ethz.ch/gander/papers/changing.pdf

/// A polynomial of degree N-1
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Polynomial<const N: usize, B: Basis, F: FiniteField> {
  pub coefficients: [F; N],
  pub basis:        B,
}

// Type state patern for polynomial bases:
pub trait Basis {
  type Data;
}

pub struct Monomial;
impl Basis for Monomial {
  type Data = ();
}

// https://en.wikipedia.org/wiki/Lagrange_polynomial
pub struct Lagrange<const N: usize, F: FiniteField> {
  pub nodes:   [F; N],
  pub weights: [F; N],
  pub L:       Box<dyn Fn(F) -> F>,
}

impl<const N: usize, F: FiniteField> Basis for Lagrange<N, F> {
  type Data = Self;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Nodes<const N: usize, F: FiniteField>([F; N]);

/// A polynomial in monomial basis
impl<const N: usize, F: FiniteField> Polynomial<N, Monomial, F> {
  // TODO check that the polynomial degree divides the field order
  pub fn new(coefficients: [F; N]) -> Self { Self { coefficients, basis: Monomial } }

  /// Convert a polynomial from monomial to Lagrange basis using the Barycentric form
  pub fn to_lagrange(&self, nodes: Nodes<N, F>) -> Polynomial<N, Lagrange<N, F>, F> {
    // check that nodes are distinct
    let mut set = HashSet::new();
    for &node in nodes.0.iter() {
      if !set.insert(node) {
        panic!("Nodes must be distinct");
      }
    }
    let mut coeffs = [F::one(); N];
    for j in 0..N {
      coeffs[j] = self.evaluate(nodes.0[j]);
    }
    Polynomial::<N, Lagrange<N, F>, F>::new(coeffs, nodes.0)
  }

  /// Evaluate the polynomial at field element x
  pub fn evaluate(&self, x: F) -> F {
    let mut result = F::zero();
    for (i, c) in self.coefficients.into_iter().enumerate() {
      result += c * x.pow(F::Storage::from(i as u32));
    }
    result
  }
}

/// A polynomial in Lagrange basis
impl<const N: usize, F: FiniteField> Polynomial<N, Lagrange<N, F>, F> {
  // TODO check that the polynomial degree divides the field order
  pub fn new(coefficients: [F; N], nodes: [F; N]) -> Self {
    let mut weights = [F::one(); N];
    for j in 0..N {
      for m in 0..N {
        if j != m {
          weights[j] *= F::one().div(nodes[j] - nodes[m]);
        }
      }
    }
    // l(x) = \Sigmm_{m}(x-x_m)
    let l = move |x: F| {
      let mut val = F::one();
      for i in 0..N {
        val *= x - nodes[i];
      }
      val
    };

    // L(x) = l(x) * \Sigma_{j=0}^{k}  (w_j / (x - x_j)) y_j
    let L = move |x: F| {
      let mut val = F::zero();
      for j in 0..N {
        // check if we are dividing by zero
        if nodes[j] == x {
          return coefficients[j];
        }
        val += coefficients[j] * weights[j] / (x - nodes[j]);
      }
      l(x) * val
    };

    let basis = Lagrange { nodes, weights, L: Box::new(L) };
    Self { coefficients, basis }
  }

  pub fn to_monomial(&self) -> Polynomial<N, Monomial, F> {
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
    let L = &self.basis.L;
    L(x)
  }
}
mod test {
  use super::*;
  use crate::field::gf_101::GF101;

  #[test]
  fn evaluation() {
    // Coefficients of the polynomial 1 + 2x + 3x^2
    let a = GF101::new(1);
    let b = GF101::new(2);
    let c = GF101::new(3);
    let polynomial = Polynomial::<3, Monomial, GF101>::new([a, b, c]);
    let y = polynomial.evaluate(GF101::new(2));
    let r = GF101::new(17);
    assert_eq!(y, r); // 1 + 2*(2) + 3(2)^2 = 17
  }

  #[test]
  fn evaluation_with_zero() {
    // Coefficients of the polynomial 1 + 3x^2
    let a = GF101::new(1);
    let b = GF101::new(0);
    let c = GF101::new(3);
    let polynomial = Polynomial::<3, Monomial, GF101>::new([a, b, c]);
    let y = polynomial.evaluate(GF101::new(0));
    let r = GF101::new(1);
    assert_eq!(y, r); // 1 + 3(0)^2 = 1
  }

  #[test]
  fn lagrange_evaluation() {
    // Coefficients of the polynomial 1 + 2x + 3x^2
    let a = GF101::new(1);
    let b = GF101::new(2);
    let c = GF101::new(3);
    let polynomial = Polynomial::<3, Monomial, GF101>::new([a, b, c]);

    // Nodes for the Lagrange basis
    let nodes = Nodes::<3, GF101>([GF101::new(1), GF101::new(2), GF101::new(3)]);
    let lagrange = polynomial.to_lagrange(nodes);
    let r = lagrange.evaluate(GF101::new(2));
    assert_eq!(r, GF101::new(17));
  }

  #[test]
  #[should_panic]
  fn non_unique_nodes() {
    // Coefficients of the polynomial 1 + 2x
    let a = GF101::new(1);
    let b = GF101::new(2);

    let polynomial = Polynomial::<2, Monomial, GF101>::new([a, b]);
    // This should panic because the nodes are not distinct
    let nodes = Nodes::<2, GF101>([GF101::new(1), GF101::new(1)]);
    let lagrange = polynomial.to_lagrange(nodes);
  }

  #[test]
  fn test_by_hand() {
    // Coefficients of the polynomial 1 + x + 2x^2
    let a = GF101::new(1);
    let b = GF101::new(1);
    let c = GF101::new(2);
    let polynomial = Polynomial::<3, Monomial, GF101>::new([a, b, c]);
    println!("monomial coefficients {:?}", polynomial.coefficients);

    // Nodes for the Lagrange basis
    let nodes = Nodes::<3, GF101>([GF101::new(1), GF101::new(3), GF101::new(2)]);

    let lagrange = polynomial.to_lagrange(nodes);
    println!("lagrange coefficients {:?}", lagrange.coefficients);
  }
}
