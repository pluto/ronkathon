use super::*;

type F = PlutoBaseField;

fn create_test_polynomial() -> MultiVarPolynomial<F> {
  // Create the polynomial:
  // 3 x^2 y^2 z^2 + 2x^2 y + 5x^2 z^2 + 4yz + 6x + 1
  let coordinates = vec![
    vec![0, 0, 0], // Constant term
    vec![1, 0, 0], // x term
    vec![0, 1, 1], // yz term
    vec![2, 0, 2], // x^2 z^2 term
    vec![2, 1, 0], // x^2 y term
    vec![2, 2, 2], // x^2 y^2 z^2 term
  ];
  let coefficients = vec![
    F::from(1), // Constant term
    F::from(6), // x term
    F::from(4), // yz term
    F::from(5), // x^2 z^2 term
    F::from(2), // x^2 y term
    F::from(3), // x^2 y^2 z^2 term
  ];
  MultiVarPolynomial::from_coordinates(coordinates, coefficients).unwrap()
}

#[test]
fn test_sumcheck_protocol() {
  let poly = create_test_polynomial();
  // While summing over binary values for the variables remember a term is non-zero only if all
  // the variables making it are 1. This way you can calculate the following:
  let expected_sum = F::from(57);
  let mut sumcheck = SumCheck::new(poly, false);
  sumcheck.run_interactive_protocol();
  assert_eq!(sumcheck.verifier.result, expected_sum);
}

#[test]
#[should_panic]
fn test_sumcheck_protocol_incorrect() {
  let poly = create_test_polynomial();
  let incorrect_sum = F::from(58); // Intentionally incorrect sum
  let mut sumcheck = SumCheck::new(poly, false);

  // Override the verifier's initial claim with the incorrect sum
  sumcheck.verifier.claim = incorrect_sum;
  sumcheck.verifier.result = incorrect_sum;

  // This should panic due to the incorrect sum
  sumcheck.run_interactive_protocol();
}
