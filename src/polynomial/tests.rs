use super::*;

#[fixture]
fn poly() -> Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>> {
  // Coefficients of the polynomial 1 + 2x + 3x^2 + 4x^3
  let a = PrimeField::<{ PlutoPrime::Base as usize }>::new(1);
  let b = PrimeField::<{ PlutoPrime::Base as usize }>::new(2);
  let c = PrimeField::<{ PlutoPrime::Base as usize }>::new(3);
  let d = PrimeField::<{ PlutoPrime::Base as usize }>::new(4);
  Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>::new(vec![a, b, c, d])
}

#[rstest]
fn evaluation(poly: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>) {
  // Should get: 1 + 2*(2) + 3*(2)^2 + 4*(2)^3 = 49
  let y = poly.evaluate(PrimeField::<{ PlutoPrime::Base as usize }>::new(2));
  let r = PrimeField::<{ PlutoPrime::Base as usize }>::new(49);
  assert_eq!(y, r);
}

#[test]
fn evaluation_with_zero() {
  // Coefficients of the polynomial 1 + 3x^2
  let a = PrimeField::<{ PlutoPrime::Base as usize }>::new(1);
  let b = PrimeField::<{ PlutoPrime::Base as usize }>::new(0);
  let c = PrimeField::<{ PlutoPrime::Base as usize }>::new(3);
  let polynomial =
    Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>::new(vec![a, b, c]);
  let y = polynomial.evaluate(PrimeField::<{ PlutoPrime::Base as usize }>::new(0));

  // Should get: 1 + 3(0)^2 = 1
  let r = PrimeField::<{ PlutoPrime::Base as usize }>::new(1);
  assert_eq!(y, r);
}

#[rstest]
fn lagrange_evaluation(poly: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>) {
  // Convert to Lagrange basis using roots of unity
  let lagrange = poly.dft();
  println!("{}", lagrange);

  // Should get: 1 + 2*(2) + 3*(2)^2 + 4*(2)^3= 49
  let r = lagrange.evaluate(PrimeField::<{ PlutoPrime::Base as usize }>::new(2));
  assert_eq!(r, PrimeField::<{ PlutoPrime::Base as usize }>::new(49));
}

#[test]
#[should_panic]
fn no_roots_of_unity() {
  // Coefficients of the polynomial 1 + 2x
  let a = PrimeField::<{ PlutoPrime::Base as usize }>::new(1);
  let b = PrimeField::<{ PlutoPrime::Base as usize }>::new(2);
  let c = PrimeField::<{ PlutoPrime::Base as usize }>::new(3);
  let polynomial =
    Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>::new(vec![a, b, c]);
  polynomial.dft();
}

#[rstest]
fn check_coefficients(poly: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>) {
  assert_eq!(poly.coefficients, [
    PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(2),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(4)
  ]);

  assert_eq!(poly.dft().coefficients, [
    PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(79),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(99),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(18)
  ]);
}

#[rstest]
fn degree(poly: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>) {
  assert_eq!(poly.degree(), 3);
}

#[rstest]
fn leading_coefficient(poly: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>) {
  assert_eq!(poly.leading_coefficient(), PrimeField::<{ PlutoPrime::Base as usize }>::new(4));
}

#[rstest]
fn pow_mult(poly: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>) {
  assert_eq!(poly.pow_mult(PrimeField::<{ PlutoPrime::Base as usize }>::new(5), 2).coefficients, [
    PrimeField::<{ PlutoPrime::Base as usize }>::new(0),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(0),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(5),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(15),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(20)
  ]);
}

#[rstest]
fn trim_zeros(mut poly: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>) {
  poly.coefficients.push(PrimeField::<{ PlutoPrime::Base as usize }>::ZERO);
  assert_eq!(poly.coefficients, [
    PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(2),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(4),
    PrimeField::<{ PlutoPrime::Base as usize }>::ZERO
  ]);
  poly.trim_zeros();
  assert_eq!(poly.coefficients, [
    PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(2),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(4)
  ]);
}

#[test]
fn trim_to_zero() {
  let poly = Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>::new(vec![
    PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
    PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
  ]);
  assert_eq!(poly.coefficients, [PrimeField::<{ PlutoPrime::Base as usize }>::ZERO]);
}

#[rstest]
fn dft(poly: Polynomial<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>) {
  assert_eq!(poly.dft().coefficients, [
    PrimeField::<{ PlutoPrime::Base as usize }>::new(10),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(79),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(99),
    PrimeField::<{ PlutoPrime::Base as usize }>::new(18)
  ]);
  let poly = Polynomial::<Monomial, PrimeField<{ PlutoPrime::Base as usize }>>::new(vec![
    PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
    PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
  ]);
  assert_eq!(poly.coefficients, [PrimeField::<{ PlutoPrime::Base as usize }>::ZERO]);
}
