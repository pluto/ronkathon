use crate::{
  algebra::field::{
    prime::PlutoBaseField,
    Field,
  },
  polynomial::multivariate_polynomial::{
    MultivariatePolynomial, MultivariateTerm, MultivariateVariable,
  },
  sumcheck::{
    verify_sumcheck_first_round, verify_sumcheck_last_round, verify_sumcheck_univariate_poly_sum,
  },
};

#[test]
#[test]
fn test_full_sumcheck_protocol() {
  // This test demonstrates the full sumcheck protocol for the polynomial:
  // f(x0, x1, x2) = x0 * (x1 + x2) - (x1 * x2)
  // We'll prove and verify the sum of this polynomial over the boolean hypercube {0,1}^3.

  // The sumcheck protocol is used to prove the sum of a multivariate polynomial over a boolean
  // hypercube without explicitly computing all 2^n evaluations. This is particularly useful for
  // large n, where computing all evaluations would be computationally infeasible.

  // Step 1: Define the polynomial
  // We start with a multivariate polynomial because the sumcheck protocol is designed to work
  // with functions over boolean inputs, which are naturally represented as multivariate
  // polynomials.
  let poly = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 1 }, MultivariateVariable {
        index:    1,
        exponent: 1,
      }],
      PlutoBaseField::ONE,
    ), // x0 * x1
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 1 }, MultivariateVariable {
        index:    2,
        exponent: 1,
      }],
      PlutoBaseField::ONE,
    ), // x0 * x2
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 1, exponent: 1 }, MultivariateVariable {
        index:    2,
        exponent: 1,
      }],
      -PlutoBaseField::ONE,
    ), // -x1 * x2
  ]);

  // Step 2: First round of the sumcheck protocol
  // The prover computes the actual sum over all boolean inputs and generates the first univariate
  // polynomial. This step is crucial because it reduces the n-variate polynomial to a univariate
  // polynomial in x0, while maintaining the property that its sum over {0,1} equals the original
  // sum.
  let (claimed_sum, univariate_poly1) = poly.prove_first_sumcheck_round();

  // The verifier checks the first round
  // This check ensures that the sum of the univariate polynomial over {0,1} equals the claimed sum.
  // It's a key step in verifying the prover's claim without computing the full sum.
  let (valid, _challenge) = verify_sumcheck_first_round(claimed_sum, &univariate_poly1);
  assert!(valid, "First round verification failed");

  // Verify that the first univariate polynomial is correct: f0(x0) = 4x0 - 1
  // This check confirms that the prover correctly computed the univariate polynomial.
  let expected_poly1 = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 0, exponent: 1 }],
      PlutoBaseField::new(4),
    ),
    MultivariateTerm::new(vec![], -PlutoBaseField::ONE),
  ]);
  assert_eq!(univariate_poly1, expected_poly1, "First round polynomial is incorrect");

  println!("Claimed sum: {:?}", claimed_sum);
  println!("First univariate polynomial: {}", univariate_poly1);

  // Step 3: Second round of the sumcheck protocol
  // The verifier sends a challenge. This challenge is used to reduce the problem further,
  // from proving a statement about a sum to proving a statement about a single evaluation.
  let random_challenge1 = PlutoBaseField::new(4);

  // The prover generates the second univariate polynomial
  // This polynomial represents the partial evaluation of the original polynomial with x0 fixed to
  // the challenge value.
  let univariate_poly2 = poly.prove_sumcheck_round_i(1, vec![random_challenge1]);
  println!("Round 2 univariate polynomial: {}", univariate_poly2);

  // Verify that the second univariate polynomial is correct: f1(x1) = 7x1 + 4
  // This check ensures that the prover correctly computed the second univariate polynomial.
  let expected_poly2 = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    MultivariateTerm::new(
      vec![MultivariateVariable { index: 1, exponent: 1 }],
      PlutoBaseField::new(7),
    ),
    MultivariateTerm::new(vec![], PlutoBaseField::new(4)),
  ]);
  assert_eq!(univariate_poly2, expected_poly2, "Second round polynomial is incorrect");

  // The verifier checks the second round
  // This check ensures that the evaluation of the first univariate polynomial at the challenge
  // point equals the sum of the second univariate polynomial over {0,1}.
  let (valid, _challenge) =
    verify_sumcheck_univariate_poly_sum(1, random_challenge1, &univariate_poly1, &univariate_poly2);
  assert!(valid, "Second round verification failed");

  // Step 4: Third (final) round of the sumcheck protocol
  // The process continues, further reducing the problem to a single point evaluation of the
  // original polynomial.
  let random_challenge2 = PlutoBaseField::new(4);

  // The prover generates the final univariate polynomial
  let univariate_poly3 =
    poly.prove_sumcheck_last_round(2, vec![random_challenge1, random_challenge2]);
  println!("Round 3 univariate polynomial: {}", univariate_poly3);

  // Verify that the final univariate polynomial is correct: f2(x2) = 16
  // This check confirms that the prover correctly computed the final univariate polynomial.
  let expected_poly3 =
    MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![MultivariateTerm::new(
      vec![],
      PlutoBaseField::new(16),
    )]);
  assert_eq!(univariate_poly3, expected_poly3, "Final round polynomial is incorrect");

  // The verifier checks the final round
  // This check ensures that the evaluation of the second univariate polynomial at the challenge
  // point equals the sum of the third univariate polynomial over {0,1}.
  let (valid, _final_challenge) =
    verify_sumcheck_univariate_poly_sum(2, random_challenge2, &univariate_poly2, &univariate_poly3);
  assert!(valid, "Final round verification failed");

  // Step 5: Final verification
  // The verifier sends a final challenge and checks the entire protocol
  // This step verifies that the final point evaluation claimed by the prover
  // matches the evaluation of the original polynomial at the challenge points.
  let random_challenge3 = PlutoBaseField::new(4);
  let valid = verify_sumcheck_last_round(
    vec![random_challenge1, random_challenge2, random_challenge3],
    &univariate_poly3,
    &poly,
  );
  assert!(valid, "Overall sumcheck protocol verification failed");

  // If we reach this point, the entire sumcheck protocol has been successfully demonstrated
  // The verifier is convinced that the prover knows the correct sum without having to compute it
  // directly.
  println!("Sumcheck protocol successfully verified!");
}
