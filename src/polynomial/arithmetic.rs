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
//! - [`Div`] for dividing two polynomials.
//! - [`Rem`] for finding the remainder of dividing two polynomials.
use super::*;

impl<F: FiniteField, const D: usize, const D2: usize> Add<Polynomial<Monomial, F, D2>>
  for Polynomial<Monomial, F, D>
{
  type Output = Self;

  /// Implements addition of two polynomials by adding their coefficients.
  /// Note: degree of first operand > deg of second operand.
  fn add(self, rhs: Polynomial<Monomial, F, D2>) -> Self {
    let coefficients = self
      .coefficients
      .iter()
      .zip(rhs.coefficients.iter().chain(std::iter::repeat(&F::ZERO)))
      .map(|(&a, &b)| a + b)
      .take(D)
      .collect::<Vec<F>>()
      .try_into()
      .unwrap_or_else(|v: Vec<F>| panic!("Expected a Vec of length {} but it was {}", D, v.len()));
    Self { coefficients, basis: self.basis }
  }
}

impl<F: FiniteField, const D: usize, const D2: usize> AddAssign<Polynomial<Monomial, F, D2>>
  for Polynomial<Monomial, F, D>
{
  /// Implements in-place addition of two polynomials by adding their coefficients.
  fn add_assign(&mut self, rhs: Polynomial<Monomial, F, D2>) { *self = *self + rhs; }
}

impl<F: FiniteField, const D: usize> Sum for Polynomial<Monomial, F, D> {
  /// Implements summing a collection of polynomials.
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self { iter.reduce(|x, y| x + y).unwrap() }
}

impl<F: FiniteField, const D: usize, const D2: usize> Sub<Polynomial<Monomial, F, D2>>
  for Polynomial<Monomial, F, D>
{
  type Output = Self;

  /// Implements subtraction of two polynomials by subtracting their coefficients.
  /// Note: degree of first operand > deg of second operand.
  fn sub(self, rhs: Polynomial<Monomial, F, D2>) -> Self {
    let coefficients = self
      .coefficients
      .iter()
      .zip(rhs.coefficients.iter().chain(std::iter::repeat(&F::ZERO)))
      .map(|(&a, &b)| a - b)
      .take(D)
      .collect::<Vec<F>>()
      .try_into()
      .unwrap_or_else(|v: Vec<F>| panic!("Expected a Vec of length {} but it was {}", D, v.len()));
    Self { coefficients, basis: self.basis }
  }
}

impl<F: FiniteField, const D: usize, const D2: usize> SubAssign<Polynomial<Monomial, F, D2>>
  for Polynomial<Monomial, F, D>
{
  /// Implements in-place subtraction of two polynomials by subtracting their coefficients.
  fn sub_assign(&mut self, rhs: Polynomial<Monomial, F, D2>) { *self = *self - rhs; }
}

impl<F: FiniteField, const D: usize> Neg for Polynomial<Monomial, F, D> {
  type Output = Self;

  /// Implements negation of a polynomial by negating its coefficients.
  fn neg(self) -> Self {
    Self {
      coefficients: self
        .coefficients
        .into_iter()
        .map(|c| -c)
        .collect::<Vec<F>>()
        .try_into()
        .unwrap_or_else(|v: Vec<F>| {
          panic!("Expected a Vec of length {} but it was {}", D, v.len())
        }),
      basis:        self.basis,
    }
  }
}

impl<F: FiniteField, const D: usize, const D2: usize> Mul<Polynomial<Monomial, F, D2>>
  for Polynomial<Monomial, F, D>
where [(); D + D2 - 1]:
{
  type Output = Polynomial<Monomial, F, { D + D2 - 1 }>;

  /// Implements multiplication of two polynomials by computing:
  /// $$
  /// (a_0 + a_1 x + a_2 x^2 + \ldots) \times (b_0 + b_1 x + b_2 x^2 + \ldots) = c_0 + c_1 x + c_2
  /// x^2
  /// + \ldots $$ where $c_i = \sum_{j=0}^{i} a_j b_{i-j}$.
  ///
  /// Note: Returns a polynomial of degree $D1+D2-1$
  fn mul(self, rhs: Polynomial<Monomial, F, D2>) -> Self::Output {
    let mut coefficients = [F::ZERO; D + D2 - 1];
    for i in 0..D {
      for j in 0..D2 {
        coefficients[i + j] += self.coefficients[i] * rhs.coefficients[j];
      }
    }
    Polynomial::<Monomial, F, { D + D2 - 1 }>::new(coefficients)
  }
}

impl<F: FiniteField, const D: usize, const D2: usize> Div<Polynomial<Monomial, F, D2>>
  for Polynomial<Monomial, F, D>
{
  type Output = Self;

  /// Implements division of two polynomials by using the [`Polynomial::quotient_and_remainder`]
  /// method. Implicitly uses the Euclidean division algorithm.
  ///
  /// Note: returns a polynomial with degree of first operand.
  fn div(self, rhs: Polynomial<Monomial, F, D2>) -> Self::Output {
    self.quotient_and_remainder(rhs).0
  }
}

impl<F: FiniteField, const D: usize, const D2: usize> Rem<Polynomial<Monomial, F, D2>>
  for Polynomial<Monomial, F, D>
{
  type Output = Self;

  /// Implements remainder of dividing two polynomials by using the
  /// [`Polynomial::quotient_and_remainder`] method. Implicitly uses the Euclidean division
  /// algorithm.
  ///
  /// Note: returns a polynomial of degree of first operand
  fn rem(self, rhs: Polynomial<Monomial, F, D2>) -> Self { self.quotient_and_remainder(rhs).1 }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[fixture]
  fn poly_a() -> Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 4> {
    Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 4>::new([
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(2),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(4),
    ])
  }

  #[fixture]
  fn poly_b() -> Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 5> {
    Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 5>::new([
      PrimeField::<{ PlutoPrime::Base as usize }>::new(5),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(6),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(7),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(8),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(9),
    ])
  }

  #[fixture]
  fn poly_c() -> Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 2> {
    Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 2>::new([
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(2),
    ])
  }

  #[fixture]
  fn poly_d() -> Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 2> {
    Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 2>::new([
      PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(4),
    ])
  }

  #[rstest]
  fn add(
    poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 4>,
    poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 5>,
  ) {
    assert_eq!((poly_b + poly_a).coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(6),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(8),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(12),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(9)
    ]);
  }

  #[rstest]
  fn add_assign(
    poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 4>,
    mut poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 5>,
  ) {
    poly_b += poly_a;
    assert_eq!(poly_b.coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(6),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(8),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(12),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(9)
    ]);
  }

  #[rstest]
  fn sum(
    poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 4>,
    poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 5>,
  ) {
    assert_eq!(
      [poly_a.coefficients.into(), poly_b]
        .into_iter()
        .sum::<Polynomial<Monomial, PrimeField::<{ PlutoPrime::Base as usize }>, 5>>()
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
    poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 4>,
    poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 5>,
  ) {
    let poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 5> =
      poly_a.coefficients.into();
    assert_eq!((poly_a - poly_b).coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(92)
    ]);

    assert_eq!((poly_b - poly_a).coefficients, [
      PlutoBaseField::new(4),
      PlutoBaseField::new(4),
      PlutoBaseField::new(4),
      PlutoBaseField::new(4),
      PlutoBaseField::new(9)
    ]);
  }

  #[rstest]
  fn sub_assign(
    poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 4>,
    poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 5>,
  ) {
    let mut poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 5> =
      poly_a.coefficients.into();
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
  fn neg(poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 4>) {
    assert_eq!((-poly_a).coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(100),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(99),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(98),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(97)
    ]);
  }

  #[rstest]
  fn div(
    poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 4>,
    poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 5>,
  ) {
    assert_eq!(
      (poly_a / poly_b).coefficients,
      [PrimeField::<{ PlutoPrime::Base as usize }>::new(0); 4]
    );
    assert_eq!((poly_b / poly_a).coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(95),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(78),
      PlutoBaseField::ZERO,
      PlutoBaseField::ZERO,
      PlutoBaseField::ZERO
    ]);

    let p = Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 3>::new([
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(2),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
    ]);
    let q = Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 2>::new([
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
    ]);
    let r = p / q;
    assert_eq!(r.coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PlutoBaseField::ZERO
    ]);
  }

  #[rstest]
  fn rem(
    poly_a: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 4>,
    poly_b: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 5>,
  ) {
    assert_eq!((poly_a % poly_b).coefficients, poly_a.coefficients);
    assert_eq!((poly_b % poly_a).coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(11),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(41),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(71),
      PlutoBaseField::ZERO,
      PlutoBaseField::ZERO,
    ]);

    let p = Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 3>::new([
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(2),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
    ]);
    let q = Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 2>::new([
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
    ]);
    let r = p % q;
    assert_eq!(r.coefficients, [PrimeField::<{ PlutoPrime::Base as usize }>::new(0); 3]);
  }

  #[rstest]
  fn mul(
    poly_a: Polynomial<Monomial, PlutoBaseField, 4>,
    poly_b: Polynomial<Monomial, PlutoBaseField, 5>,
    poly_c: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 2>,
    poly_d: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>, 2>,
  ) {
    assert_eq!((poly_a * poly_b).coefficients, [
      PlutoBaseField::new(5),
      PlutoBaseField::new(16),
      PlutoBaseField::new(34),
      PlutoBaseField::new(60),
      PlutoBaseField::new(70),
      PlutoBaseField::new(70),
      PlutoBaseField::new(59),
      PlutoBaseField::new(36)
    ]);
    assert_eq!((poly_c * poly_d).coefficients, [
      PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(8)
    ]);
  }

  //   #[rstest]
  //   fn mul_assign(
  //     mut poly_c: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  //     poly_d: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  //   ) {
  //     poly_c *= poly_d;
  //     assert_eq!(poly_c.coefficients, [
  //       PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
  //       PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
  //       PrimeField::<{ PlutoPrime::Base as usize }>::new(8)
  //     ]);
  //   }

  //   #[rstest]
  //   fn product(
  //     poly_c: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  //     poly_d: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>,
  //   ) {
  //     assert_eq!(
  //       [poly_c, poly_d]
  //         .into_iter()
  //         .product::<Polynomial<Monomial, PrimeField::<{ PlutoPrime::Base as usize }>>>()
  //         .coefficients,
  //       [
  //         PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
  //         PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
  //         PrimeField::<{ PlutoPrime::Base as usize }>::new(8)
  //       ]
  //     );
  //   }
}
