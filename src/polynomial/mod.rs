use super::*;

pub mod arithmetic;
#[cfg(test)] mod tests;

// https://people.inf.ethz.ch/gander/papers/changing.pdf

/// A polynomial of arbitrary degree.
/// Allows for a choice of basis between [`Monomial`] and [`Lagrange`].
/// The coefficients are stored in a vector with the zeroth degree term first.
/// Highest degree term should be non-zero.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Polynomial<B: Basis, F: FiniteField> {
  pub coefficients: Vec<F>,
  pub basis:        B,
}

/// [`Basis`] trait is used to specify the basis of the polynomial.
/// The basis can be [`Monomial`] or [`Lagrange`]. This is a type-state pattern for [`Polynomial`].
pub trait Basis {
  type Data;
}

/// [`Monomial`] is a struct that implements the [`Basis`] trait.
/// It is used to specify the [monomial basis](https://en.wikipedia.org/wiki/Monomial_basis) for a polynomial.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Monomial;
impl Basis for Monomial {
  type Data = ();
}

/// [`Lagrange`] is a struct that implements the [`Basis`] trait.
/// It is used to specify the [lagrange basis](https://en.wikipedia.org/wiki/Lagrange_polynomial) for a polynomial.
/// It requires a vector of field elements that are the nodes (evaluation points) used to create the
/// Lagrange basis.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Lagrange<F: FiniteField> {
  pub nodes: Vec<F>,
}
impl<F: FiniteField> Basis for Lagrange<F> {
  type Data = Self;
}

impl<B: Basis, F: FiniteField> Polynomial<B, F> {
  /// A polynomial in any basis has a fixed number of independent terms.
  /// For example, in [`Monomial`] basis, the number of terms is one more than the degree of the
  /// polynomial.
  ///
  /// ## Arguments:
  /// - `self`: The polynomial in any basis.
  ///
  /// ## Returns:
  /// - The number of terms in the polynomial as `usize`.
  pub fn num_terms(&self) -> usize { self.coefficients.len() }
}

impl<F: FiniteField> Polynomial<Monomial, F> {
  /// Create a new polynomial in [`Monomial`] basis.
  ///
  /// ## Arguments:
  /// - `coefficients`: A vector of field elements representing the coefficients of the polynomial
  ///   on each monomial term, e.g., x^0, x^1, ....
  ///
  /// ## Returns:
  /// - A new polynomial in [`Monomial`] basis with the given coefficients.
  /// - The polynomial is automatically simplified to have a non-zero leading coefficient, that is
  ///   coefficient on the highest power term x^d.
  pub fn new(coefficients: Vec<F>) -> Self {
    let mut poly = Self { coefficients, basis: Monomial };
    // Remove trailing zeros in the `coefficients` vector so that the highest degree term is
    // non-zero.
    poly.trim_zeros();
    poly
  }

  fn trim_zeros(&mut self) {
    let last_nonzero_index = self.coefficients.iter().rposition(|&c| c != F::ZERO);
    match last_nonzero_index {
      Some(index) => self.coefficients.truncate(index + 1),
      None => self.coefficients.truncate(1),
    }
  }

  /// Gets the degree of the polynomial in the [`Monomial`] [`Basis`].
  /// ## Arguments:
  /// - `self`: The polynomial in the [`Monomial`] [`Basis`].
  ///
  /// ## Returns:
  /// - The degree of the polynomial as a `usize`.
  pub fn degree(&self) -> usize { self.coefficients.len() - 1 }

  /// Retrieves the coefficient on the highest degree monomial term of a polynomial in the
  /// [`Monomial`] [`Basis`].
  pub fn leading_coefficient(&self) -> F { *self.coefficients.last().unwrap() }

  /// Evaluates the polynomial at a given [`FiniteField`] element `x` using the [`Monomial`] basis.
  /// This is not using Horner's method or any other optimization.
  ///
  /// ## Arguments:
  /// - `x`: The field element at which to evaluate the polynomial.
  ///
  /// ## Returns:
  /// - The result of evaluating the polynomial at `x` which is an element of the associated
  ///   [`FiniteField`].
  pub fn evaluate(&self, x: F) -> F {
    let mut result = F::ZERO;
    for (i, c) in self.coefficients.iter().enumerate() {
      result += *c * x.pow(i as u64);
    }
    result
  }

  /// Accessory function that allows for the multiplication of a polynomial by a scalar `coeff`
  /// times a monomial `x^pow`.
  /// Used explicitly in the [`Polynomial::quotient_and_remainder`] function for implementing the
  /// [Euclidean division](https://en.wikipedia.org/wiki/Euclidean_division) algorithm (to implement [`Div`] and [`Rem`] traits).
  ///
  /// ## Arguments:
  /// - `coeff`: The scalar to multiply the polynomial by.
  /// - `pow`: The power of the monomial to multiply the polynomial by.
  ///
  /// ## Returns:
  /// - A new polynomial in the [`Monomial`] [`Basis`] that is the result of multiplying the
  ///   polynomial by `coeff` times `x^pow`.
  pub fn pow_mult(&self, coeff: F, pow: usize) -> Polynomial<Monomial, F> {
    let mut coefficients = vec![F::ZERO; self.coefficients.len() + pow];
    self.coefficients.iter().enumerate().for_each(|(i, c)| {
      coefficients[i + pow] = *c * coeff;
    });
    Polynomial::<Monomial, F>::new(coefficients)
  }

  /// [Euclidean division](https://en.wikipedia.org/wiki/Euclidean_division) of two polynomials in [`Monomial`] basis.
  /// Used explicitly in implementing the [`Div`] and [`Rem`] traits.
  ///
  /// ## Arguments:
  /// - `self`: The dividend polynomial in [`Monomial`] basis.
  /// - `rhs`: The divisor polynomial in [`Monomial`] basis.
  ///
  /// ## Returns:
  /// - A tuple of two polynomials in [`Monomial`] basis:
  ///   - The first element is the quotient polynomial.
  ///   - The second element is the remainder polynomial.
  fn quotient_and_remainder(self, rhs: Self) -> (Self, Self) {
    // Initial quotient value
    let mut q = Self::new(vec![]);

    // Initial remainder value is our numerator polynomial
    let mut p = self.clone();

    // Leading coefficient of the denominator
    let c = rhs.leading_coefficient();

    // Create quotient polynomial
    let mut diff = p.degree() as isize - rhs.degree() as isize;
    if diff < 0 {
      return (Self::new(vec![F::ZERO]), p);
    }
    let mut q_coeffs = vec![F::ZERO; diff as usize + 1];

    // Perform the repeated long division algorithm
    while diff >= 0 {
      let s = p.leading_coefficient() * c.inverse().unwrap();
      q_coeffs[diff as usize] = s;
      p -= rhs.pow_mult(s, diff as usize);
      p.trim_zeros();
      diff = p.degree() as isize - rhs.degree() as isize;
    }
    q.coefficients = q_coeffs;
    (q, p)
  }

  /// Computes the [Discrete Fourier Transform](https://en.wikipedia.org/wiki/Discrete_Fourier_transform)
  /// of the polynomial in the [`Monomial`] basis by evaluating the polynomial at the roots of
  /// unity.
  /// This also converts a polynomial from [`Monomial`] to [`Lagrange`] [`Basis`] with node points
  /// given by the roots of unity.
  ///
  /// ## Returns:
  /// - A new polynomial in the [`Lagrange`] [`Basis`] that is the result of converting the
  ///  evaluation of the polynomial at the roots of unity.
  ///
  /// ## Panics
  /// - This function will panic in calling [`FiniteField::primitive_root_of_unity`] if the field
  /// does not have roots of unity for the degree of the polynomial.
  pub fn dft(&self) -> Polynomial<Lagrange<F>, F> {
    let n = self.num_terms();
    let primitive_root_of_unity = F::primitive_root_of_unity(F::Storage::from(n as u32));

    Polynomial::<Lagrange<F>, F>::new(
      (0..n)
        .map(|i| {
          self.coefficients.iter().enumerate().fold(F::ZERO, |acc, (j, &coeff)| {
            acc + coeff * primitive_root_of_unity.pow(i as u64 * j as u64)
          })
        })
        .collect(),
    )
  }
}

impl Display for Polynomial<Monomial, GF101> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    let mut first = true;
    for (i, c) in self.coefficients.iter().enumerate() {
      if !first {
        write!(f, " + ")?;
      }
      first = false;
      if i == 0 {
        write!(f, "{}", c)?;
      } else {
        write!(f, "{}x^{}", c, i)?;
      }
    }
    Ok(())
  }
}

impl<F: FiniteField> Polynomial<Lagrange<F>, F> {
  /// Create a new polynomial in [`Lagrange`] basis by supplying a number of coefficients.
  /// Assumes that a field has a root of unity for the amount of terms given in the coefficients.
  ///
  /// ## Arguments:
  /// - `coefficients`: A vector of field elements representing the coefficients of the polynomial
  ///  in the [`Lagrange`] basis.
  ///
  /// ## Returns:
  /// - A new polynomial in the [`Lagrange`] basis with the given coefficients.
  ///
  /// ## Panics
  /// - This function will panic if the field does not have roots of unity for the length of the
  ///   polynomial.
  pub fn new(coefficients: Vec<F>) -> Self {
    // Check that the polynomial degree divides the field order so that there are roots of unity.
    let n = coefficients.len();
    assert_eq!(
      (F::ORDER - F::Storage::from(1_u32)) % F::Storage::from(n as u32),
      F::Storage::from(0)
    );
    let primitive_root = F::primitive_root_of_unity(F::Storage::from(n as u32));
    let nodes: Vec<F> = (0..n).map(|i| primitive_root.pow(i as u64)).collect();

    Self { coefficients, basis: Lagrange { nodes } }
  }

  /// Evaluate the polynomial in the [`Lagrange`] basis at a given field element `x`.
  /// This is done by evaluating the Lagrange polynomial at `x` using the nodes of the Lagrange
  /// basis. The Lagrange polynomial is given by:
  /// $$
  /// L(x) = \sum_{j=0}^{n-1} \left( \frac{w_j}{x - x_j} \right) y_j
  /// $$
  /// where $w_j = \prod_{m \neq j} (x_j - x_m)^{-1}$ and $y_j$ are the coefficients of the
  /// polynomial. The evaluation of the polynomial at `x` is then given by $L(x)$.
  ///
  /// ## Arguments:
  /// - `x`: The field element as [`FiniteField`] at which to evaluate the polynomial.
  ///
  /// ## Returns:
  /// - The result of evaluating the polynomial at `x` which is an element of the associated
  ///  [`FiniteField`].
  pub fn evaluate(&self, x: F) -> F {
    let n = self.coefficients.len();

    // w_j = \Pi_{m \neq j} (x_j - x_m)^{-1}
    let mut weights = vec![F::ONE; n];
    weights.iter_mut().enumerate().for_each(|(idx, w)| {
      for m in 0..n {
        if idx != m {
          *w *= F::ONE.div(self.basis.nodes[idx] - self.basis.nodes[m]);
        }
      }
    });

    // l(x) = \Pi_{i=0}^{n-1} (x - x_i)
    let l = move |x: F| {
      let mut val = F::ONE;
      for i in 0..n {
        val *= x - self.basis.nodes[i];
      }
      val
    };

    // L(x) = l(x) * \Sigma_{j=0}^{n-1}  (w_j / (x - x_j)) y_j
    l(x)
      * weights.iter().zip(self.coefficients.iter()).zip(self.basis.nodes.iter()).fold(
        F::ZERO,
        |acc, ((w, &c), &n)| {
          if n == x {
            return c;
          }
          acc + c * *w / (x - n)
        },
      )
  }
}

impl Display for Polynomial<Lagrange<GF101>, GF101> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    let d = self.num_terms() - 1;
    for (idx, (coeff, node)) in self.coefficients.iter().zip(self.basis.nodes.iter()).enumerate() {
      if idx == d {
        write!(f, "{}*l_{}(x)", coeff, node)?;
        break;
      }
      write!(f, "{}*l_{}(x) + ", coeff, node)?;
    }
    Ok(())
  }
}
