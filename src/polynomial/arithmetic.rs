//! Arithmetic operations for polynomials.
//! The operations are implemented a [`Polynomial`] in the [`Monomial`] basis for now.
//!
//! ## Implementations
//! - [`Add`] for adding two polynomials.
//! - [`AddAssign`] for adding two polynomials in place.
//! - [`Sum`] for summing a collection of polynomials.
//! - [`Sub`] for subtracting two polynomials.
//! - [`SubAssign`] for subtracting two polynomials in place.
//! - [`Neg`] for negating a polynomial.
//! - [`Mul`] for multiplying two polynomials.
//! - [`MulAssign`] for multiplying two polynomials in place.
//! - [`Product`] for multiplying a collection of polynomials.
//! - [`Div`] for dividing two polynomials.
//! - [`Rem`] for finding the remainder of dividing two polynomials.
use super::*;

/// Implements addition of two polynomials by adding their coefficients.
impl<F: FiniteField> Add for Polynomial<Monomial, F> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self {
    let d = self.coefficients.len().max(rhs.coefficients.len());
    let coefficients = self
      .coefficients
      .iter()
      .chain(std::iter::repeat(&F::ZERO))
      .zip(rhs.coefficients.iter().chain(std::iter::repeat(&F::ZERO)))
      .map(|(&a, &b)| a + b)
      .take(d)
      .collect();
    Self { coefficients, basis: self.basis }
  }
}

/// Implements in-place addition of two polynomials by adding their coefficients.
impl<F: FiniteField> AddAssign for Polynomial<Monomial, F> {
  fn add_assign(&mut self, mut rhs: Self) {
    let d = self.degree().max(rhs.degree());
    if self.degree() < d {
      self.coefficients.resize(d + 1, F::ZERO);
    } else {
      rhs.coefficients.resize(d + 1, F::ZERO);
    }
    for i in 0..d + 1 {
      self.coefficients[i] += rhs.coefficients[i];
    }
  }
}

/// Implements summing a collection of polynomials.
impl<F: FiniteField> Sum for Polynomial<Monomial, F> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self { iter.reduce(|x, y| x + y).unwrap() }
}

/// Implements subtraction of two polynomials by subtracting their coefficients.
impl<F: FiniteField> Sub for Polynomial<Monomial, F> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let d = self.coefficients.len().max(rhs.coefficients.len());
    let coefficients = self
      .coefficients
      .iter()
      .chain(std::iter::repeat(&F::ZERO))
      .zip(rhs.coefficients.iter().chain(std::iter::repeat(&F::ZERO)))
      .map(|(&a, &b)| a - b)
      .take(d)
      .collect();
    Self { coefficients, basis: self.basis }
  }
}

/// Implements in-place subtraction of two polynomials by subtracting their coefficients.
impl<F: FiniteField> SubAssign for Polynomial<Monomial, F> {
  fn sub_assign(&mut self, mut rhs: Self) {
    let d = self.degree().max(rhs.degree());
    if self.degree() < d {
      self.coefficients.resize(d + 1, F::ZERO);
    } else {
      rhs.coefficients.resize(d + 1, F::ZERO);
    }
    for i in 0..d + 1 {
      self.coefficients[i] -= rhs.coefficients[i];
    }
  }
}

/// Implements negation of a polynomial by negating its coefficients.
impl<F: FiniteField> Neg for Polynomial<Monomial, F> {
  type Output = Self;

  fn neg(self) -> Self {
    Self {
      coefficients: self.coefficients.into_iter().map(|c| -c).collect(),
      basis:        self.basis,
    }
  }
}

/// Implements multiplication of two polynomials by computing:
/// $$
/// (a_0 + a_1 x + a_2 x^2 + \ldots) \times (b_0 + b_1 x + b_2 x^2 + \ldots) = c_0 + c_1 x + c_2 x^2
/// + \ldots $$ where $c_i = \sum_{j=0}^{i} a_j b_{i-j}$.
impl<F: FiniteField> Mul for Polynomial<Monomial, F> {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self {
    let d = self.degree() + rhs.degree();
    let mut coefficients = vec![F::ZERO; d + 1];
    for i in 0..self.degree() + 1 {
      for j in 0..rhs.degree() + 1 {
        coefficients[i + j] += self.coefficients[i] * rhs.coefficients[j];
      }
    }
    Self { coefficients, basis: self.basis }
  }
}

/// Implements in-place multiplication of two polynomials by using the [`Mul`] implementation.
impl<F: FiniteField> MulAssign for Polynomial<Monomial, F> {
  fn mul_assign(&mut self, rhs: Self) {
    let cloned = self.clone();
    self.coefficients = (cloned * rhs).coefficients;
  }
}

/// Implements product of a collection of polynomials by using the [`Mul`] implementation.
impl<F: FiniteField> Product for Polynomial<Monomial, F> {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self { iter.reduce(|x, y| x * y).unwrap() }
}

/// Implements division of two polynomials by using the [`Polynomial::quotient_and_remainder`]
/// method. Implicitly uses the Euclidean division algorithm.
impl<F: FiniteField> Div for Polynomial<Monomial, F> {
  type Output = Self;

  fn div(self, rhs: Self) -> Self::Output { self.quotient_and_remainder(rhs).0 }
}

/// Implements remainder of dividing two polynomials by using the
/// [`Polynomial::quotient_and_remainder`] method. Implicitly uses the Euclidean division algorithm.
impl<F: FiniteField> Rem for Polynomial<Monomial, F> {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self { self.quotient_and_remainder(rhs).1 }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[fixture]
  fn poly_a() -> Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>> {
    Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>::new(vec![
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(2),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(4),
    ])
  }

  #[fixture]
  fn poly_b() -> Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>> {
    Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>::new(vec![
      PrimeField::<{ PlutoPrime::Base as usize }>::new(5),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(6),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(7),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(8),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(9),
    ])
  }

  #[fixture]
  fn poly_c() -> Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>> {
    Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>::new(vec![
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(2),
    ])
  }

  #[fixture]
  fn poly_d() -> Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>> {
    Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>::new(vec![
      PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(4),
    ])
  }

  #[rstest]
  fn add(
    poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
    poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  ) {
    assert_eq!((poly_a + poly_b).coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(6),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(8),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(12),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(9)
    ]);
  }

  #[rstest]
  fn add_assign(
    mut poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
    poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  ) {
    poly_a += poly_b;
    assert_eq!(poly_a.coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(6),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(8),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(12),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(9)
    ]);
  }

  #[rstest]
  fn sum(
    poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
    poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  ) {
    assert_eq!(
      [poly_a, poly_b]
        .into_iter()
        .sum::<Polynomial<Monomial, PrimeField::<{ PlutoPrime::Base as usize }>>>()
        .coefficients,
      [
        PrimeField::<{ PlutoPrime::Base as usize }>::new(6),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(8),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(12),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(9)
      ]
    );
  }

  #[rstest]
  fn sub(
    poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
    poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  ) {
    assert_eq!((poly_a - poly_b).coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(92)
    ]);
  }

  #[rstest]
  fn sub_assign(
    mut poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
    poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  ) {
    poly_a -= poly_b;
    assert_eq!(poly_a.coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(92)
    ]);
  }

  #[rstest]
  fn neg(poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>) {
    assert_eq!((-poly_a).coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(100),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(99),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(98),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97)
    ]);
  }

  #[rstest]
  fn div(
    poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
    poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  ) {
    assert_eq!((poly_a.clone() / poly_b.clone()).coefficients, [PrimeField::<
      { PlutoPrime::Base as usize },
    >::new(0)]);
    assert_eq!((poly_b / poly_a).coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(95),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(78)
    ]);

    let p = Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>::new(vec![
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(2),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
    ]);
    let q = Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>::new(vec![
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
    ]);
    let r = p / q;
    assert_eq!(r.coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1)
    ]);
  }

  #[rstest]
  fn rem(
    poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
    poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  ) {
    assert_eq!((poly_a.clone() % poly_b.clone()).coefficients, poly_a.coefficients);
    assert_eq!((poly_b % poly_a).coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(11),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(41),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(71)
    ]);

    let p = Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>::new(vec![
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(2),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
    ]);
    let q = Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>::new(vec![
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
    ]);
    let r = p % q;
    assert_eq!(r.coefficients, [PrimeField::<{ PlutoPrime::Base as usize }>::new(0)]);
  }

  #[rstest]
  fn mul(
    poly_c: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
    poly_d: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  ) {
    assert_eq!((poly_c * poly_d).coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(8)
    ]);
  }

  #[rstest]
  fn mul_assign(
    mut poly_c: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
    poly_d: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  ) {
    poly_c *= poly_d;
    assert_eq!(poly_c.coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(8)
    ]);
  }

  #[rstest]
  fn product(
    poly_c: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
    poly_d: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  ) {
    assert_eq!(
      [poly_c, poly_d]
        .into_iter()
        .product::<Polynomial<Monomial, PrimeField::<{ PlutoPrime::Base as usize }>>>()
        .coefficients,
      [
        PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(8)
      ]
    );
  }
}
