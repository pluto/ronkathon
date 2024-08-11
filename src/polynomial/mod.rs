//! This module contains the implementation of polynomials in the [`Monomial`] and [`Lagrange`]
//! bases.
//! ## Overview
//! A polynomial is a mathematical expression that consists of variables and coefficients. The
//! variables are raised to non-negative integer powers and multiplied by the coefficients. For
//! example, the polynomial $f(x) = 1 + 2x + 3x^2 + 4x^3$ has coefficients $1, 2, 3, 4$ in the
//! [`Monomial`] [`Basis`].
//!
//! - [`Polynomial`] struct represents a polynomial in any basis. These are generic over the
//!   [`Basis`] and [`FiniteField`] traits.
//! - [`Basis`] trait is used to specify the basis of the polynomial which can be either:
//!    - [`Monomial`] basis as shown above.
//!    - [`Lagrange`] basis which is used in the [Lagrange interpolation](https://en.wikipedia.org/wiki/Lagrange_polynomial).
//! - Includes arithmetic operations such as addition, subtraction, multiplication, and division in
//!   the [`arithmetic`] module. The [`Polynomial`] struct is generic over the [`Basis`] and
//!   [`FiniteField`] traits.
//! - Includes Discrete Fourier Transform (DFT) for polynomials in the [`Monomial`] basis to convert
//!   into the [`Lagrange`] basis via evaluation at the roots of unity.

use std::array;

use super::*;
use crate::algebra::field::FiniteField;

pub mod arithmetic;
#[cfg(test)] mod tests;

// https://people.inf.ethz.ch/gander/papers/changing.pdf

/// A polynomial of arbitrary degree `D-1`.
/// Allows for a choice of basis between [`Monomial`] and [`Lagrange`].
/// The coefficients are stored in a vector with the zeroth degree term first.
/// Highest degree term should be non-zero.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Polynomial<B: Basis, F: FiniteField, const D: usize> {
  /// Coefficients of the polynomial in the chosen basis.
  /// These will be in either:
  /// - Increasing order of degree for [`Monomial`] basis.
  /// - Order of the nodes of the Lagrange polynomial for [`Lagrange`] basis.
  pub coefficients: [F; D],

  /// The basis of the polynomial. Additional node points are stored for [`Lagrange`] basis.
  pub basis: B,
}

/// [`Basis`] trait is used to specify the basis of the polynomial.
/// The basis can be [`Monomial`] or [`Lagrange`]. This is a type-state pattern for [`Polynomial`].
pub trait Basis {
  /// The associated data type for the basis.
  type Data;
}

/// [`Monomial`] is a struct that implements the [`Basis`] trait.
/// It is used to specify the [monomial basis](https://en.wikipedia.org/wiki/Monomial_basis) for a polynomial.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
  /// Nodes (evaluation points) of the [`Lagrange`] [`Basis`].
  pub nodes: Vec<F>,
}
impl<F: FiniteField> Basis for Lagrange<F> {
  type Data = Self;
}

impl<B: Basis, F: FiniteField, const D: usize> Polynomial<B, F, D> {
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

impl<F: FiniteField, const D: usize> Polynomial<Monomial, F, D> {
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
  pub fn new(coefficients: [F; D]) -> Self { Self { coefficients, basis: Monomial } }

  /// Helper method to remove leading zeros from coefficients
  fn trim_zeros(coefficients: &mut Vec<F>) {
    while coefficients.last().cloned() == Some(F::ZERO) {
      coefficients.pop();
    }
  }

  /// Gets the degree of the polynomial in the [`Monomial`] [`Basis`].
  /// ## Arguments:
  /// - `self`: The polynomial in the [`Monomial`] [`Basis`].
  ///
  /// ## Returns:
  /// - The degree of the polynomial as a `usize`.
  pub fn degree(&self) -> usize {
    self.coefficients.iter().rposition(|&coeff| coeff != F::ZERO).unwrap_or(0)
  }

  /// Retrieves the coefficient on the highest degree monomial term of a polynomial in the
  /// [`Monomial`] [`Basis`].
  // pub const fn leading_coefficient(&self) -> F { *self.coefficients.last().unwrap() }
  pub fn leading_coefficient(&self) -> F {
    self.coefficients.iter().rev().find(|&&coeff| coeff != F::ZERO).copied().unwrap_or(F::ZERO)
  }

  /// Evaluates the polynomial at a given [`FiniteField`] element `x` using the [`Monomial`]
  /// basis. This is not using Horner's method or any other optimization.
  ///
  /// ## Arguments:
  /// - `x`: The field element at which to evaluate the polynomial.
  ///
  /// ## Returns:
  /// - The result of evaluating the polynomial at `x` which is an element of the associated
  ///   [`FiniteFiniteField`].
  pub fn evaluate(&self, x: F) -> F {
    let mut result = F::ZERO;
    for (i, c) in self.coefficients.iter().enumerate() {
      result += *c * x.pow(i);
    }
    result
  }

  /// Accessory function that allows for the multiplication of a polynomial by a scalar `coeff`
  /// times a monomial `x^pow`.
  /// Used explicitly in the [`Polynomial::quotient_and_remainder`] function for implementing the
  /// [Euclidean division](https://en.wikipedia.org/wiki/Euclidean_division) algorithm (to implement [`Div`] and [`Rem`] traits).
  ///
  /// ## Arguments:
  /// - `const D2`: The degree of the term to multiply by, e.g., `D2==5` multiplies by `x^5`.
  /// - `coeff`: The scalar to multiply the polynomial by.
  ///
  /// ## Returns:
  /// - A new polynomial in the [`Monomial`] [`Basis`] that is the result of multiplying the
  ///   polynomial by `coeff` times `x^pow`.
  pub fn pow_mult<const D2: usize>(&self, coeff: F) -> Polynomial<Monomial, F, { D + D2 }> {
    let coefficients: [F; D + D2] =
      array::from_fn(|i| if i >= D2 { self.coefficients[i - D2] * coeff } else { F::ZERO });
    Polynomial::<Monomial, F, { D + D2 }>::new(coefficients)
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
  fn quotient_and_remainder<const D2: usize>(
    self,
    rhs: Polynomial<Monomial, F, D2>,
  ) -> (Self, Self) {
    // Initial quotient value
    let mut q_coeffs = vec![F::ZERO; D];

    // Initial remainder value is our numerator polynomial
    let mut p_coeffs = self.coefficients.to_vec();

    // Leading coefficient of the denominator
    let c = rhs.leading_coefficient();

    // Perform the repeated long division algorithm
    while p_coeffs.iter().filter(|&&x| x != F::ZERO).count() > 0
      && p_coeffs.len() >= rhs.coefficients.len()
    {
      // find degree of dividend, divisor
      let p_degree = p_coeffs.iter().rposition(|&x| x != F::ZERO).unwrap();
      let rhs_degree = rhs.coefficients.iter().rposition(|&x| x != F::ZERO).unwrap();

      if p_degree < rhs_degree {
        break;
      }

      let diff = p_degree - rhs_degree;
      let s = p_coeffs[p_degree] * c.inverse().unwrap();
      q_coeffs[diff] = s;

      for (i, &coeff) in rhs.coefficients.iter().enumerate() {
        p_coeffs[diff + i] -= coeff * s;
      }

      Polynomial::<Monomial, F, D>::trim_zeros(&mut p_coeffs);
    }

    let quotient = Polynomial {
      coefficients: q_coeffs.try_into().unwrap_or_else(|v: Vec<F>| {
        let mut arr = [F::ZERO; D];
        arr.copy_from_slice(&v[..D]);
        arr
      }),
      basis:        self.basis,
    };

    let remainder = Polynomial {
      coefficients: p_coeffs.try_into().unwrap_or_else(|v: Vec<F>| {
        let mut arr = [F::ZERO; D];
        arr[..v.len()].copy_from_slice(&v[..]);
        arr
      }),
      basis:        self.basis,
    };

    (quotient, remainder)
  }

  /// Computes the [Discrete Fourier Transform](https://en.wikipedia.org/wiki/Discrete_Fourier_transform)
  /// of the polynomial in the [`Monomial`] basis by evaluating the polynomial at the roots of
  /// unity.
  /// This also converts a polynomial from [`Monomial`] to [`Lagrange`] [`Basis`] with node points
  /// given by the roots of unity.
  ///
  /// ## Returns:
  /// - A new polynomial in the [`Lagrange`] [`Basis`] that is the result of converting the
  ///   evaluation of the polynomial at the roots of unity.
  ///
  /// ## Panics
  /// - This function will panic in calling [`FiniteField::primitive_root_of_unity`] if the field
  ///   does not have roots of unity for the degree of the polynomial.
  pub fn dft(&self) -> Polynomial<Lagrange<F>, F, D> {
    let n = self.num_terms();
    let primitive_root_of_unity = F::primitive_root_of_unity(n);

    let coeffs: Vec<F> = (0..n)
      .map(|i| {
        self
          .coefficients
          .iter()
          .enumerate()
          .fold(F::ZERO, |acc, (j, &coeff)| acc + coeff * primitive_root_of_unity.pow(i * j))
      })
      .collect();
    Polynomial::<Lagrange<F>, F, D>::new(
      coeffs.try_into().unwrap_or_else(|v: Vec<F>| {
        panic!("Expected a Vec of length {} but it was {}", D, v.len())
      }),
    )
  }
}

impl<const P: usize, const D: usize> Display for Polynomial<Monomial, PrimeField<P>, D> {
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

impl<F: FiniteField, const D: usize> Polynomial<Lagrange<F>, F, D> {
  /// Create a new polynomial in [`Lagrange`] basis by supplying a number of coefficients.
  /// Assumes that a field has a root of unity for the amount of terms given in the coefficients.
  ///
  /// ## Arguments:
  /// - `coefficients`: A vector of field elements representing the coefficients of the polynomial
  ///   in the [`Lagrange`] basis.
  ///
  /// ## Returns:
  /// - A new polynomial in the [`Lagrange`] basis with the given coefficients.
  ///
  /// ## Panics
  /// - This function will panic if the field does not have roots of unity for the length of the
  ///   polynomial.
  pub fn new(coefficients: [F; D]) -> Self {
    // Check that the polynomial degree divides the field order so that there are roots of unity.
    let n = coefficients.len();
    assert_eq!((F::ORDER - 1) % n, 0);
    let primitive_root = F::primitive_root_of_unity(n);
    let nodes: Vec<F> = (0..n).map(|i| primitive_root.pow(i)).collect();

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
  ///   [`FiniteField`].
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

impl<const P: usize, const D: usize> Display
  for Polynomial<Lagrange<PrimeField<P>>, PrimeField<P>, D>
{
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

impl<const N: usize, F: FiniteField, const D: usize> From<[F; N]> for Polynomial<Monomial, F, D> {
  /// Convert from an array of field elements into a polynomial in the [`Monomial`] basis.
  ///
  /// **Note**: if new polynomial degree > old, then copy till old else pad new polynomial with zero
  fn from(coeffs: [F; N]) -> Self {
    let mut new_coeffs = [F::ZERO; D];

    let copy_size = if N < D { N } else { D };
    new_coeffs[..copy_size].copy_from_slice(&coeffs[..copy_size]);

    Self { coefficients: new_coeffs, basis: Monomial }
  }
}

impl<const N: usize, const P: usize, const D: usize> From<GaloisField<N, P>>
  for Polynomial<Monomial, PrimeField<P>, D>
{
  /// Convert from an [`GaloisField`] field element into a polynomial in the [`Monomial`] basis.
  fn from(ext: GaloisField<N, P>) -> Self { Self::from(ext.coeffs) }
}
