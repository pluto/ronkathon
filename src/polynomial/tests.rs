use super::*;

#[fixture]
fn poly() -> Polynomial<Monomial, GF101> {
  // Coefficients of the polynomial 1 + 2x + 3x^2 + 4x^3
  let a = GF101::new(1);
  let b = GF101::new(2);
  let c = GF101::new(3);
  let d = GF101::new(4);
  Polynomial::<Monomial, GF101>::new(vec![a, b, c, d])
}

#[rstest]
fn evaluation(poly: Polynomial<Monomial, GF101>) {
  // Should get: 1 + 2*(2) + 3*(2)^2 + 4*(2)^3 = 49
  let y = poly.evaluate(GF101::new(2));
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

#[rstest]
fn lagrange_evaluation(poly: Polynomial<Monomial, GF101>) {
  // Convert to Lagrange basis using roots of unity
  let lagrange = poly.dft();
  println!("{}", lagrange);

  // Should get: 1 + 2*(2) + 3*(2)^2 + 4*(2)^3= 49
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
  polynomial.dft();
}

#[rstest]
fn check_coefficients(poly: Polynomial<Monomial, GF101>) {
  assert_eq!(poly.coefficients, [GF101::new(1), GF101::new(2), GF101::new(3), GF101::new(4)]);

  assert_eq!(poly.dft().coefficients, [
    GF101::new(10),
    GF101::new(79),
    GF101::new(99),
    GF101::new(18)
  ]);
}

#[rstest]
fn degree(poly: Polynomial<Monomial, GF101>) {
  assert_eq!(poly.degree(), 3);
}

#[rstest]
fn leading_coefficient(poly: Polynomial<Monomial, GF101>) {
  assert_eq!(poly.leading_coefficient(), GF101::new(4));
}

#[rstest]
fn pow_mult(poly: Polynomial<Monomial, GF101>) {
  assert_eq!(poly.pow_mult(GF101::new(5), 2).coefficients, [
    GF101::new(0),
    GF101::new(0),
    GF101::new(5),
    GF101::new(10),
    GF101::new(15),
    GF101::new(20)
  ]);
}

#[rstest]
fn trim_zeros(mut poly: Polynomial<Monomial, GF101>) {
  poly.coefficients.push(GF101::ZERO);
  assert_eq!(poly.coefficients, [
    GF101::new(1),
    GF101::new(2),
    GF101::new(3),
    GF101::new(4),
    GF101::ZERO
  ]);
  poly.trim_zeros();
  assert_eq!(poly.coefficients, [GF101::new(1), GF101::new(2), GF101::new(3), GF101::new(4)]);
}

#[test]
fn trim_to_zero() {
  let poly = Polynomial::<Monomial, GF101>::new(vec![GF101::ZERO, GF101::ZERO]);
  assert_eq!(poly.coefficients, [GF101::ZERO]);
}

#[rstest]
fn dft(poly: Polynomial<Monomial, GF101>) {
  assert_eq!(poly.dft().coefficients, [
    GF101::new(10),
    GF101::new(79),
    GF101::new(99),
    GF101::new(18)
  ]);
  let poly = Polynomial::<Monomial, GF101>::new(vec![GF101::ZERO, GF101::ZERO]);
  assert_eq!(poly.coefficients, [GF101::ZERO]);
}
