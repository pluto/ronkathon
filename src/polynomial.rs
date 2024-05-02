use p3_field::Field;

/// A polynomial of degree N-1
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Polynomial<const N: usize, B: Basis, F: Field> {
  pub coefficients: [F; N],
  pub basis:        B,
}

pub trait Basis {
  type Data;
}

pub struct Monomial;
impl Basis for Monomial {
  type Data = ();
}
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

impl<const N: usize, F: Field> Polynomial<N, Monomial, F> {
  pub fn new(coefficients: [F; N]) -> Self { Self { coefficients, basis: Monomial } }

  /// Convert a polynomial from monomial to Lagrange basis using the Barycentric form
  pub fn to_lagrange(&self, nodes: Nodes<N, F>) -> Polynomial<N, Lagrange<N, F>, F> {
    let mut coeffs = [F::one(); N];
    for j in 0..N {
      coeffs[j] = self.evaluate(nodes.0[j]);
    }
    Polynomial::<N, Lagrange<N, F>, F>::new(coeffs, nodes.0)
  }

  pub fn evaluate(&self, x: F) -> F {
    let mut result = F::zero();
    for (i, c) in self.coefficients.into_iter().enumerate() {
      result += c * x.exp_u64(i as u64);
    }
    result
  }
}
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
        val += coefficients[j] * weights[j] / (x - nodes[j]);
      }
      l(x) * val
    };

    let basis = Lagrange { nodes, weights, L: Box::new(L) };
    Self { coefficients, basis }
  }

  pub fn evaluate(&self, x: F) -> F {
    let L = &self.basis.L;
    L(x)
  }
}
