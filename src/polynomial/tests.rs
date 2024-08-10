use super::*;
use crate::polynomial::multivariate_polynomial::{MultivariatePolynomial, MultivariateTerm, MultivariateVariable};

#[fixture]
fn poly() -> Polynomial<Monomial, PlutoBaseField, 4> {
  // Coefficients of the polynomial 1 + 2x + 3x^2 + 4x^3
  let a = PlutoBaseField::new(1);
  let b = PlutoBaseField::new(2);
  let c = PlutoBaseField::new(3);
  let d = PlutoBaseField::new(4);
  Polynomial::<Monomial, PlutoBaseField, 4>::new([a, b, c, d])
}

#[rstest]
fn evaluation(poly: Polynomial<Monomial, PlutoBaseField, 4>) {
  // Should get: 1 + 2*(2) + 3*(2)^2 + 4*(2)^3 = 49
  let y = poly.evaluate(PlutoBaseField::new(2));
  let r = PlutoBaseField::new(49);
  assert_eq!(y, r);
}

#[test]
fn evaluation_with_zero() {
  // Coefficients of the polynomial 1 + 3x^2
  let a = PlutoBaseField::new(1);
  let b = PlutoBaseField::new(0);
  let c = PlutoBaseField::new(3);
  let polynomial = Polynomial::<Monomial, PlutoBaseField, 3>::new([a, b, c]);
  let y = polynomial.evaluate(PlutoBaseField::new(0));

  // Should get: 1 + 3(0)^2 = 1
  let r = PlutoBaseField::new(1);
  assert_eq!(y, r);
}

#[rstest]
fn lagrange_evaluation(poly: Polynomial<Monomial, PlutoBaseField, 4>) {
  // Convert to Lagrange basis using roots of unity
  let lagrange = poly.dft();
  println!("{}", lagrange);

  // Should get: 1 + 2*(2) + 3*(2)^2 + 4*(2)^3= 49
  let r = lagrange.evaluate(PlutoBaseField::new(2));
  assert_eq!(r, PlutoBaseField::new(49));
}

#[test]
#[should_panic]
fn no_roots_of_unity() {
  // Coefficients of the polynomial 1 + 2x
  let a = PlutoBaseField::new(1);
  let b = PlutoBaseField::new(2);
  let c = PlutoBaseField::new(3);
  let polynomial = Polynomial::<Monomial, PlutoBaseField, 3>::new([a, b, c]);
  polynomial.dft();
}

#[rstest]
fn check_coefficients(poly: Polynomial<Monomial, PlutoBaseField, 4>) {
  assert_eq!(poly.coefficients, [
    PlutoBaseField::new(1),
    PlutoBaseField::new(2),
    PlutoBaseField::new(3),
    PlutoBaseField::new(4)
  ]);

  assert_eq!(poly.dft().coefficients, [
    PlutoBaseField::new(10),
    PlutoBaseField::new(79),
    PlutoBaseField::new(99),
    PlutoBaseField::new(18)
  ]);
}

#[rstest]
fn degree(poly: Polynomial<Monomial, PlutoBaseField, 4>) {
  assert_eq!(poly.degree(), 3);
}

#[rstest]
fn leading_coefficient(poly: Polynomial<Monomial, PlutoBaseField, 4>) {
  assert_eq!(poly.leading_coefficient(), PlutoBaseField::new(4));
}

#[rstest]
fn pow_mult(poly: Polynomial<Monomial, PlutoBaseField, 4>) {
  assert_eq!(
    poly.pow_mult::<2>(PlutoBaseField::new(5)),
    Polynomial::<Monomial, PlutoBaseField, 6>::new([
      PlutoBaseField::new(0),
      PlutoBaseField::new(0),
      PlutoBaseField::new(5),
      PlutoBaseField::new(10),
      PlutoBaseField::new(15),
      PlutoBaseField::new(20)
    ])
  );
}

#[test]
fn trim_zeros() {
  let mut coefficients = vec![
    PlutoBaseField::new(1),
    PlutoBaseField::new(2),
    PlutoBaseField::new(3),
    PlutoBaseField::new(4),
    PlutoBaseField::ZERO,
  ];
  Polynomial::<Monomial, PlutoBaseField, 5>::trim_zeros(coefficients.as_mut());
  assert_eq!(coefficients, [
    PlutoBaseField::new(1),
    PlutoBaseField::new(2),
    PlutoBaseField::new(3),
    PlutoBaseField::new(4)
  ]);
}

#[rstest]
fn dft(poly: Polynomial<Monomial, PlutoBaseField, 4>) {
  assert_eq!(poly.dft().coefficients, [
    PlutoBaseField::new(10),
    PlutoBaseField::new(79),
    PlutoBaseField::new(99),
    PlutoBaseField::new(18)
  ]);
  // let poly =
  //   Polynomial::<Monomial, PlutoBaseField>::new(vec![PlutoBaseField::ZERO,
  // PlutoBaseField::ZERO]); assert_eq!(poly.coefficients, [PlutoBaseField::ZERO]);
}

#[test]
fn test_multivariate_polynomial_creation() {
  let poly = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 2 }, MultivariateVariable { index: 1, exponent: 1 }],
      PlutoBaseField::new(3)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 1 }],
      PlutoBaseField::new(2)
    ),
    MultivariateTerm::new(
      vec![],
      PlutoBaseField::new(1)
    )
  ]);

  assert_eq!(poly.degree(), 3);

  assert_eq!(
    poly.variables().into_iter().collect::<std::collections::HashSet<_>>(),
    vec![0, 1].into_iter().collect::<std::collections::HashSet<_>>()
  );
}

#[test]
fn test_multivariate_polynomial_addition() {
  let poly1 = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 2 }],
      PlutoBaseField::new(1)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 1, exponent: 1 }],
      PlutoBaseField::new(2)
    )
  ]);

  let poly2 = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 2 }],
      PlutoBaseField::new(3)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 2, exponent: 1 }],
      PlutoBaseField::new(4)
    )
  ]);

  let result = poly1 + poly2;

  println!("Addition Result polynomial: {}", result);

  let expected_result = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 2 }],
      PlutoBaseField::new(4)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 1, exponent: 1 }],
      PlutoBaseField::new(2)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 2, exponent: 1 }],
      PlutoBaseField::new(4)
    )
  ]);

  assert_eq!(result, expected_result);
}

#[test]
fn test_multivariate_polynomial_multiplication() {
  let poly1 = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 1 }],
      PlutoBaseField::new(2)
    ),
    MultivariateTerm::new(
      vec![],
      PlutoBaseField::new(1)
    )
  ]);

  let poly2 = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 1, exponent: 1 }],
      PlutoBaseField::new(3)
    ),
    MultivariateTerm::new(
      vec![],
      PlutoBaseField::new(1)
    )
  ]);

  let result = poly1 * poly2;

  println!("Multiplication Result polynomial: {}", result);

  let expected_result = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 1 }, MultivariateVariable { index: 1, exponent: 1 }],
      PlutoBaseField::new(6)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 1 }],
      PlutoBaseField::new(2)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 1, exponent: 1 }],
      PlutoBaseField::new(3)
    ),
    MultivariateTerm::new(
      vec![],
      PlutoBaseField::new(1)
    )
  ]);

  assert_eq!(result, expected_result);
}

#[test]
fn test_multivariate_polynomial_evaluation() {
  let poly = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 2 }, MultivariateVariable { index: 1, exponent: 1 }],
      PlutoBaseField::new(3)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 1 }],
      PlutoBaseField::new(2)
    ),
    MultivariateTerm::new(
      vec![],
      PlutoBaseField::new(1)
    )
  ]);

  let points = vec![(0, PlutoBaseField::new(2)), (1, PlutoBaseField::new(3))];

  println!("{}", poly);

  let result = poly.evaluate(&points);
  // 3*(2^2)*(3) + 2*(2) + 1 = 3*4*3 + 4 + 1 = 36 + 4 + 1 = 41
  assert_eq!(result, PlutoBaseField::new(41));
}

#[test]
fn test_apply_variables_single_variable() {
  let poly = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 2 }],
      PlutoBaseField::new(3)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 1 }],
      PlutoBaseField::new(2)
    ),
    MultivariateTerm::new(
      vec![],
      PlutoBaseField::new(1)
    )
  ]);

  let variables = vec![(0, PlutoBaseField::new(2))];
  let result = poly.apply_variables(&variables);

  let expected_result = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![],
      PlutoBaseField::new(17)
    )
  ]);

  assert_eq!(result, expected_result);
}

#[test]
fn test_apply_variables_multiple_variables() {
  let poly = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 2 }, MultivariateVariable { index: 1, exponent: 1 }],
      PlutoBaseField::new(3)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 1 }],
      PlutoBaseField::new(2)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 1, exponent: 1 }],
      PlutoBaseField::new(4)
    ),
    MultivariateTerm::new(
      vec![],
      PlutoBaseField::new(1)
    )
  ]);

  println!("Apply Multiple Variables Polynomial: {}", poly);

  let variables = vec![(0, PlutoBaseField::new(2)), (1, PlutoBaseField::new(3))];
  let result = poly.apply_variables(&variables);

  println!("Reduced Multiple Variable Polynomial: {}", result);

  let expected_result = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![],
      PlutoBaseField::new(53)
    )
  ]);

  assert_eq!(result, expected_result);
}

#[test]
fn test_apply_variables_partial_application() {
  let poly = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![
          MultivariateVariable { index: 0, exponent: 2 },
          MultivariateVariable { index: 1, exponent: 1 },
          MultivariateVariable { index: 2, exponent: 1 }
      ],
      PlutoBaseField::new(3)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 1 }, MultivariateVariable { index: 2, exponent: 1 }],
      PlutoBaseField::new(2)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 1, exponent: 1 }],
      PlutoBaseField::new(4)
    )
  ]);

  let variables = vec![(0, PlutoBaseField::new(2)), (1, PlutoBaseField::new(3))];
  let applied_poly = poly.apply_variables(&variables);

  let expected_result = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 2, exponent: 1 }],
      PlutoBaseField::new(40)
    ),
    MultivariateTerm::new(
      vec![],
      PlutoBaseField::new(12)
    )
  ]);

  assert_eq!(applied_poly, expected_result);
}

#[test]
fn test_apply_variables_no_effect() {
  let poly = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 2 }, MultivariateVariable { index: 1, exponent: 1 }],
      PlutoBaseField::new(3)
    ),
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 2, exponent: 1 }],
      PlutoBaseField::new(2)
    )
  ]);

  let variables = vec![(3, PlutoBaseField::new(5))];
  let result = poly.apply_variables(&variables);

  assert_eq!(result, poly);
}

#[test]
fn test_apply_variables_empty() {
  let poly = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 2 }, MultivariateVariable { index: 1, exponent: 1 }],
      PlutoBaseField::new(3)
    )
  ]); // 3x_0^2*x_1

  let variables = vec![];
  let result = poly.apply_variables(&variables);

  assert_eq!(result, poly);
}
