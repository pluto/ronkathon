use std::collections::HashSet;

use p3_field::Field;

/// A polynomial of degree N-1
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Polynomial<const N: usize, B: Basis, F: Field> {
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
pub struct Lagrange<const N: usize, F: Field> {
  pub nodes:   [F; N],
  pub weights: [F; N],
  pub L:       Box<dyn Fn(F) -> F>,
}

impl<const N: usize, F: Field> Basis for Lagrange<N, F> {
  type Data = Self;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Nodes<const N: usize, F: Field>([F; N]);

/// A polynomial in monomial basis
impl<const N: usize, F: Field> Polynomial<N, Monomial, F> {
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
      result += c * x.exp_u64(i as u64);
    }
    result
  }
}

/// A polynomial in Lagrange basis
impl<const N: usize, F: Field> Polynomial<N, Lagrange<N, F>, F> {
  pub fn new(coefficients: [F; N], nodes: [F; N]) -> Self {
    let mut weights = [F::one(); N];
    for j in 0..N {
      for m in 0..N {
        if j != m {
          weights[j] *= F::one().div(nodes[j] - nodes[m]);
        }
      }
    }
    let l = move |x: F| {
      let mut val = F::one();
      for i in 0..N {
        val *= x - nodes[i];
      }
      val
    };
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

  /// Evaluate the polynomial at field element x
  pub fn evaluate(&self, x: F) -> F {
    let L = &self.basis.L;
    L(x)
  }
}

mod test {
  use super::*;
  use crate::field::PlutoField;

  #[test]
  fn evaluation() {
    // Coefficients of the polynomial 1 + 2x + 3x^2
    let a = PlutoField::new(1);
    let b = PlutoField::new(2);
    let c = PlutoField::new(3);
    let polynomial = Polynomial::<3, Monomial, PlutoField>::new([a, b, c]);
    let y = polynomial.evaluate(PlutoField::new(2));
    let r = PlutoField::new(17);
    assert_eq!(y, r); // 1 + 2*(2) + 3(2)^2 = 17
  }

  #[test]
  fn evaluation_with_zero() {
    // Coefficients of the polynomial 1 + 3x^2
    let a = PlutoField::new(1);
    let b = PlutoField::new(0);
    let c = PlutoField::new(3);
    let polynomial = Polynomial::<3, Monomial, PlutoField>::new([a, b, c]);
    let y = polynomial.evaluate(PlutoField::new(0));
    let r = PlutoField::new(1);
    assert_eq!(y, r); // 1 + 3(0)^2 = 1
  }

  #[test]
  fn lagrange_evaluation() {
    // Coefficients of the polynomial 1 + 2x + 3x^2
    let a = PlutoField::new(1);
    let b = PlutoField::new(2);
    let c = PlutoField::new(3);
    let polynomial = Polynomial::<3, Monomial, PlutoField>::new([a, b, c]);

    // Nodes for the Lagrange basis
    let nodes =
      Nodes::<3, PlutoField>([PlutoField::new(1), PlutoField::new(2), PlutoField::new(3)]);
    let lagrange = polynomial.to_lagrange(nodes);
    let r = lagrange.evaluate(PlutoField::new(2));
    assert_eq!(r, PlutoField::new(17));
  }

  #[test]
  #[should_panic]
  fn non_unique_nodes() {
    // Coefficients of the polynomial 1 + 2x
    let a = PlutoField::new(1);
    let b = PlutoField::new(2);

    let polynomial = Polynomial::<2, Monomial, PlutoField>::new([a, b]);
    // This should panic because the nodes are not distinct
    let nodes = Nodes::<2, PlutoField>([PlutoField::new(1), PlutoField::new(1)]);
    let lagrange = polynomial.to_lagrange(nodes);
  }
}
