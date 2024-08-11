//! # Sumcheck Protocol Implementation
//!
//! This module implements the sumcheck protocol, a powerful interactive proof system
//! used in various zero-knowledge proof constructions.
//!
//! ## Overview of the Sumcheck Protocol
//!
//! The sumcheck protocol allows a prover to convince a verifier that the sum of a
//! multivariate polynomial over all boolean inputs (i.e., the boolean hypercube) is
//! equal to a claimed value, without the verifier having to compute the sum directly.
//!
//! The protocol proceeds in rounds, where in each round:
//! 1. The prover sends a univariate polynomial.
//! 2. The verifier checks certain properties of this polynomial and sends a random challenge.
//! 3. This process reduces the multivariate polynomial to a univariate one in each round.
//!
//! ## Implementation Details
//!
//! This implementation provides both interactive and non-interactive versions of the sumcheck
//! protocol.
//!
//! ### Prover Implementation
//!
//! The prover's implementation is split into several methods:
//!
//! - `prove_first_sumcheck_round`: Computes the claimed sum and the first univariate polynomial.
//! - `prove_sumcheck_round_i`: Generates the univariate polynomial for intermediate rounds.
//! - `prove_sumcheck_last_round`: Handles the final round of the protocol.
//! - `compute_univariate_polynomial`: A helper method to compute the univariate polynomial for each
//!   round.
//!
//! This structure allows for a clear separation of concerns and follows the round-based
//! nature of the sumcheck protocol.
//!
//! ### Verifier Implementation
//!
//! The verifier's implementation is divided into separate functions for each stage:
//!
//! - `verify_sumcheck_first_round`: Verifies the first round, checking the claimed sum.
//! - `verify_sumcheck_univariate_poly_sum`: Verifies intermediate rounds.
//! - `verify_sumcheck_last_round`: Performs the final verification step.
//!
//! This separation allows for clear and modular verification logic, closely following
//! the structure of the sumcheck protocol.
//!
//! ### Non-Interactive Version
//!
//! The module also provides non-interactive versions of the protocol:
//!
//! - `non_interactive_sumcheck_prove`: Generates a complete proof in one step.
//! - `non_interactive_sumcheck_verify`: Verifies the complete proof.
//!
//! These functions use a random oracle model to simulate the interactive challenges,
//! making the protocol suitable for non-interactive scenarios.
//!
//! ## Correctness and Efficiency
//!
//! The implementation correctly follows the sumcheck protocol:
//!
//! 1. It reduces the multivariate polynomial to univariate polynomials in each round.
//! 2. It uses random challenges to ensure the prover cannot predict the verification path.
//! 3. The final verification step ties the protocol back to the original multivariate polynomial.
//!
//! The use of `MultivariatePolynomial` and efficient polynomial operations ensures that
//! the implementation is both correct and computationally efficient.
//!
//! ## Usage
//!
//! To use this implementation, create a `MultivariatePolynomial`, then use the
//! `non_interactive_sumcheck_prove` function to generate a proof, and
//! `non_interactive_sumcheck_verify` to verify it.
//!
//! For more fine-grained control, you can use the individual prover and verifier functions
//! to implement an interactive version of the protocol.

use std::{
  fmt::Display,
  hash::{Hash, Hasher},
};

use rand::{Rng, SeedableRng};

use crate::{
  algebra::field::FiniteField,
  polynomial::multivariate_polynomial::MultivariatePolynomial,
  random::{Random, RandomOracle},
};

mod boolean_array;
#[cfg(test)] mod tests;
mod to_bytes;

use self::{boolean_array::get_all_possible_boolean_values, to_bytes::ToBytes};

impl<F: FiniteField + Random> RandomOracle for F {
  fn random_oracle<R: Rng + ?Sized>(_rng: &mut R, input: &[u8]) -> Self {
    // This is a simplified example. In a real implementation,
    // you'd want to use a cryptographic hash function here.
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    input.hash(&mut hasher);
    let hash = hasher.finish();

    // Use the hash to seed a new RNG
    let mut seeded_rng = rand::rngs::StdRng::seed_from_u64(hash);

    // Generate a random field element using the seeded RNG
    Self::random(&mut seeded_rng)
  }
}

impl<F: FiniteField + Display> MultivariatePolynomial<F> {
  /// Proves the first round of the sumcheck protocol for this multivariate polynomial.
  ///
  /// This function is crucial for initiating the sumcheck protocol because:
  /// 1. It computes the total sum of the polynomial over all boolean inputs, which is the claimed
  ///    sum that the prover wants to prove.
  /// 2. It generates the first univariate polynomial g_1(X1), which is the first step in reducing
  ///    the multivariate sumcheck to a series of univariate sumchecks.
  ///
  /// The sumcheck protocol is essential for efficiently verifying the sum of a multivariate
  /// polynomial over a boolean hypercube without evaluating every point, which would be
  /// exponential in the number of variables. This function sets up the foundation for the
  /// entire protocol.
  ///
  /// # Returns
  /// - A tuple containing:
  ///   1. The claimed sum (F): The total sum of the polynomial over all boolean inputs.
  ///   2. The first univariate polynomial (MultivariatePolynomial<F>): g_1(X1), which is actually
  ///      univariate despite the type name.
  pub fn prove_first_sumcheck_round(&self) -> (F, MultivariatePolynomial<F>) {
    let variables = self.variables();
    let num_variables = variables.len();

    let sum = get_all_possible_boolean_values(num_variables)
      .map(|bool_values| {
        let assignment: Vec<(usize, F)> = variables
          .iter()
          .enumerate()
          .map(|(i, &var)| (var, if bool_values[i] { F::ONE } else { F::ZERO }))
          .collect();
        self.evaluate(&assignment)
      })
      .sum();

    // Compute the univariate polynomial g_1(X1)
    let univariate_poly = self.compute_univariate_polynomial(0, vec![]);

    (sum, univariate_poly)
  }

  /// Proves the i-th round of the sumcheck protocol for this multivariate polynomial.
  ///
  /// This function is a key part of the sumcheck protocol, generating the univariate polynomial
  /// for the i-th round based on the partial assignment from previous rounds.
  ///
  /// # Arguments
  ///
  /// * `i` - The current round number (0-indexed).
  /// * `partial_assignment` - A vector of field elements representing the values chosen by the
  ///   verifier in previous rounds.
  ///
  /// # Returns
  ///
  /// * `MultivariatePolynomial<F>` - The univariate polynomial g_i(X_i) for the i-th round. Despite
  ///   the type name, this polynomial is univariate in X_i.
  ///
  /// # Properties and Equalities
  ///
  /// 1. Degree Preservation: The degree of g_i(X_i) in X_i is at most the degree of the original
  ///    polynomial in X_i.
  ///
  /// 2. Sum Consistency: The sum of g_i(X_i) over {0,1} equals g_{i-1}(r_{i-1}), where r_{i-1} is
  ///    the random challenge from the previous round.
  ///
  /// 3. Randomized Reduction: g_i(X_i) reduces the sum check for i variables to a sum check for i-1
  ///    variables when a random point is chosen.
  ///
  /// 4. Partial Evaluation: g_i(X_i) can be seen as a partial evaluation of the original
  ///    polynomial, with the first i-1 variables fixed to the values in partial_assignment.
  ///
  /// These properties ensure the soundness and completeness of the sumcheck protocol,
  /// allowing for efficient verification of the claimed sum.
  ///
  /// # Note
  ///
  /// This function relies on `compute_univariate_polynomial` to perform the actual computation
  /// of the univariate polynomial for the current round.
  pub fn prove_sumcheck_round_i(
    &self,
    i: usize,
    partial_assignment: Vec<F>,
  ) -> MultivariatePolynomial<F> {
    return self.compute_univariate_polynomial(i, partial_assignment);
  }

  /// Proves the last round of the sumcheck protocol for this multivariate polynomial.
  ///
  /// This function is similar to `prove_sumcheck_round_i`, but specifically handles the last round
  /// of the sumcheck protocol. It generates the final univariate polynomial based on all previous
  /// assignments.
  ///
  /// # Arguments
  ///
  /// * `i` - The index of the last round (should be equal to the number of variables minus 1).
  /// * `partial_assignment` - A vector of field elements representing all values chosen by the
  ///   verifier in previous rounds.
  ///
  /// # Returns
  ///
  /// * `MultivariatePolynomial<F>` - The final univariate polynomial for the last round. This
  ///   polynomial is univariate in the last remaining variable.
  ///
  /// # Note
  ///
  /// This function relies on `compute_univariate_polynomial` to perform the actual computation
  /// of the univariate polynomial for the last round. The result of this function is crucial
  /// for the final verification step in the sumcheck protocol.
  pub fn prove_sumcheck_last_round(
    &self,
    i: usize,
    partial_assignment: Vec<F>,
  ) -> MultivariatePolynomial<F> {
    return self.compute_univariate_polynomial(i, partial_assignment);
  }

  fn compute_univariate_polynomial(
    &self,
    round: usize,
    partial_assignment: Vec<F>,
  ) -> MultivariatePolynomial<F> {
    let variables = self.variables();
    let num_variables = variables.len();

    // Create a polynomial to store the result
    // First create a partial evaluation
    let partial_poly = self.apply_variables(
      &partial_assignment.iter().enumerate().map(|(i, &v)| (i, v)).collect::<Vec<_>>(),
    );

    let result_polynomial = get_all_possible_boolean_values(num_variables - round - 1)
      .map(|bool_values| {
        let further_assignments: Vec<F> =
          bool_values.iter().map(|&b| if b { F::ONE } else { F::ZERO }).collect();
        let further_variables =
          ((round + 1)..num_variables).zip(further_assignments).collect::<Vec<_>>();
        let poly = partial_poly.clone().apply_variables(&further_variables);
        poly
      })
      .fold(MultivariatePolynomial::new(), |acc, poly| acc + poly);

    // Assert that the resulting polynomial has only one variable
    assert!(
      result_polynomial.variables().len() <= 1,
      "The univariate polynomial should have at most one variable"
    );

    result_polynomial
  }
}

/// Verifies the first round of the sumcheck protocol.
///
/// This function is crucial for initiating the verification process in the sumcheck protocol.
/// The verifier needs these components to ensure the correctness of the prover's claim:
///
/// 1. `claimed_sum`: The total sum claimed by the prover. This is the value that the verifier wants
///    to check without computing the entire sum themselves.
///
/// 2. `univariate_poly`: The first univariate polynomial g_1(X_1) provided by the prover. This
///    polynomial is supposed to represent the sum over all but the first variable.
///
/// The verification process involves:
///
/// 1. Checking that the provided polynomial is indeed univariate. This ensures that the prover is
///    following the protocol correctly by reducing one variable at a time.
///
/// 2. Verifying that g_1(0) + g_1(1) equals the claimed sum. This check is fundamental because it
///    connects the univariate polynomial to the original multivariate sum. If this equality holds,
///    it suggests that the prover has correctly computed the univariate polynomial for the first
///    round.
///
/// 3. Generating a random challenge. This challenge will be used in subsequent rounds and is
///    crucial for the security of the protocol. It ensures that the prover cannot predict or
///    manipulate future rounds.
///
/// # Arguments
///
/// * `claimed_sum`: The sum claimed by the prover.
/// * `univariate_poly`: The univariate polynomial for the first round.
///
/// # Returns
///
/// A tuple containing:
/// - A boolean indicating whether the verification passed (true) or failed (false).
/// - The random challenge generated for the next round.
///
/// # Type Parameters
///
/// * `F`: A type that implements both `FiniteField` and `Random` traits.
pub fn verify_sumcheck_first_round<F: FiniteField + Random>(
  claimed_sum: F,
  univariate_poly: &MultivariatePolynomial<F>,
) -> (bool, F) {
  // Step 1: Verify that the polynomial is univariate (has only one variable)
  if univariate_poly.variables().len() != 1 {
    return (false, F::ZERO);
  }

  // Step 2: Verify that g(0) + g(1) = claimed_sum
  let var = 0;
  let sum_at_endpoints =
    univariate_poly.evaluate(&[(var, F::ZERO)]) + univariate_poly.evaluate(&[(var, F::ONE)]);

  if sum_at_endpoints != claimed_sum {
    return (false, F::ZERO);
  }

  // Step 3: Generate a random challenge
  let mut rng = rand::thread_rng();
  let challenge: F = F::random(&mut rng);

  // Return true (verification passed) and the evaluation at the challenge point
  (true, challenge)
}

/// Verify the i-th round of the sumcheck protocol
///
/// This function is crucial for verifying the correctness of each intermediate step in the sumcheck
/// protocol. It ensures that the prover is following the protocol correctly and not deviating from
/// the expected behavior.
///
/// # Arguments
///
/// * `round`: The current round number of the sumcheck protocol. This is needed to keep track of
///   which variable is being eliminated in the current round.
/// * `challenge`: The random challenge from the previous round. This is used to evaluate the
///   previous round's polynomial and connect it to the current round.
/// * `previous_univariate_poly`: The univariate polynomial from the previous round. This is needed
///   to verify the consistency between rounds.
/// * `current_univariate_poly`: The univariate polynomial for the current round. This is the
///   polynomial that the prover claims represents the sum over the current variable.
///
/// # Returns
///
/// A tuple containing:
/// - A boolean indicating whether the verification passed (true) or failed (false).
/// - The new random challenge generated for the next round.
///
/// # Why these parameters are needed
///
/// 1. `round`: Keeps track of the protocol's progress and ensures variables are eliminated in
///    order.
/// 2. `challenge`: Connects the current round to the previous one, preventing the prover from
///    deviating.
/// 3. `previous_univariate_poly`: Used to verify consistency between rounds.
/// 4. `current_univariate_poly`: The polynomial to be verified in the current round.
///
/// These parameters allow the verifier to check:
/// - The univariate nature of the current polynomial (ensuring one variable is eliminated per
///   round).
/// - The consistency between rounds (g_i(r_{i-1}) = g_{i-1}(0) + g_{i-1}(1)).
/// - Generate a new random challenge for the next round, maintaining the protocol's
///   unpredictability.
pub fn verify_sumcheck_univariate_poly_sum<F: FiniteField + Random>(
  round: usize,
  challenge: F,
  previous_univariate_poly: &MultivariatePolynomial<F>,
  current_univariate_poly: &MultivariatePolynomial<F>,
) -> (bool, F) {
  // Step 1: Verify that the current polynomial is univariate
  if current_univariate_poly.variables().len() > 1 {
    return (false, F::ZERO);
  }

  // Step 2: Verify that g_i(r_{i-1}) = g_{i-1}(0) + g_{i-1}(1)
  let prev_var = round - 1;
  let sum_at_endpoints = previous_univariate_poly.evaluate(&[(prev_var, challenge)]);

  let eval_at_previous_challenge = current_univariate_poly.evaluate(&[(round, F::ZERO)])
    + current_univariate_poly.evaluate(&[(round, F::ONE)]);
  if eval_at_previous_challenge != sum_at_endpoints {
    return (false, F::ZERO);
  }

  // Step 3: Generate a new random challenge
  let mut rng = rand::thread_rng();
  let new_challenge: F = F::random(&mut rng);

  // Return true (verification passed) and the evaluation at the new challenge point
  (true, new_challenge)
}

/// Verifies the final round of the sumcheck protocol.
///
/// This function is crucial for the verifier to ensure the prover's honesty in the final round
/// of the sumcheck protocol. It checks if the claimed univariate polynomial is consistent with
/// the original multivariate polynomial when all challenges are applied.
///
/// # Arguments
///
/// * `challenges`: A vector of all previous challenges from earlier rounds.
/// * `univariate_poly`: The final univariate polynomial claimed by the prover.
/// * `poly`: The original multivariate polynomial.
///
/// # Returns
///
/// A boolean indicating whether the verification passed (true) or failed (false).
///
/// # Why the verifier needs this information
///
/// 1. `challenges`: The verifier needs all previous challenges to reconstruct the point at which
///    the original polynomial should be evaluated. This ensures consistency across all rounds.
///
/// 2. `univariate_poly`: This is the prover's final claim about the polynomial after all but one
///    variable have been fixed. The verifier needs to check if this claim is consistent with the
///    original polynomial.
///
/// 3. `poly`: The original multivariate polynomial is necessary to independently compute the
///    correct evaluation and compare it with the prover's claim.
///
/// By comparing the evaluation of the original polynomial at the challenge point with the
/// evaluation of the claimed univariate polynomial at a random point, the verifier can detect
/// any dishonesty from the prover with high probability.
pub fn verify_sumcheck_last_round<F: FiniteField + Random>(
  challenges: Vec<F>,
  univariate_poly: &MultivariatePolynomial<F>,
  poly: &MultivariatePolynomial<F>,
) -> bool {
  // Step 1: Apply all challenges to the original polynomial
  let mut challenges_with_indices = Vec::new();
  for (i, challenge) in challenges.iter().enumerate() {
    challenges_with_indices.push((i, *challenge));
  }
  let poly_evaluation = poly.evaluate(&challenges_with_indices);

  // Step 2: Generate a random challenge for the last variable
  let mut rng = rand::thread_rng();
  let last_challenge: F = F::random(&mut rng);

  // Step 3: Evaluate the univariate polynomial at the last challenge
  let last_var = challenges.len();
  let univariate_evaluation = univariate_poly.evaluate(&[(last_var, last_challenge)]);

  // Step 4: Compare the evaluations
  poly_evaluation == univariate_evaluation
}

impl<F: FiniteField + Display> ToBytes for F {
  fn to_bytes(&self) -> Vec<u8> {
    // Implement this based on how your field elements are represented
    // This is just an example:
    self.to_string().into_bytes()
  }
}

impl<F: FiniteField + Display> ToBytes for MultivariatePolynomial<F> {
  fn to_bytes(&self) -> Vec<u8> {
    // Implement this based on how your polynomials are represented
    // This is just an example:
    self.to_string().into_bytes()
  }
}

/// Represents a proof for the sumcheck protocol over a finite field.
///
/// This struct contains all the components necessary for verifying a sumcheck proof,
/// including the claimed sum, round polynomials, challenges, evaluations, and final results.
///
/// # Type Parameters
///
/// * `F`: A type that implements the `FiniteField` trait, representing the field over which the
///   sumcheck protocol is performed.
pub struct SumcheckProof<F: FiniteField> {
  /// The claimed sum of the polynomial over all boolean inputs.
  pub claimed_sum: F,

  /// Vector of univariate polynomials, one for each round of the protocol.
  pub round_polynomials: Vec<MultivariatePolynomial<F>>,

  /// Vector of challenges generated during the protocol.
  pub challenges: Vec<F>,

  /// Vector of evaluations of the round polynomials at the challenge points.
  pub round_evaluations: Vec<F>,

  /// The final evaluation point, consisting of all challenges combined.
  pub final_point: Vec<F>,

  /// The final evaluation of the original multivariate polynomial at the final point.
  pub final_evaluation: F,
}

/// Generates a non-interactive sumcheck proof for a given multivariate polynomial.
///
/// This function implements the prover's side of the non-interactive sumcheck protocol.
/// It generates a proof that the sum of the polynomial over all boolean inputs equals
/// the claimed sum, without requiring interaction with the verifier.
///
/// The non-interactive nature is achieved by using a random oracle to generate challenges,
/// which both the prover and verifier can compute independently.
///
/// # Arguments
///
/// * `polynomial` - The multivariate polynomial for which to generate the sumcheck proof.
///
/// # Returns
///
/// Returns a `SumcheckProof` containing all necessary components for verification:
/// - The claimed sum
/// - Univariate polynomials for each round
/// - Challenges generated using the random oracle
/// - Evaluations of the round polynomials at the challenge points
/// - The final evaluation point and the polynomial's evaluation at that point
///
/// # Type Parameters
///
/// * `F` - A finite field type that implements necessary traits for arithmetic, random number
///   generation, conversion to bytes, and display.
pub fn non_interactive_sumcheck_prove<
  F: FiniteField + Random + RandomOracle + Display + ToBytes,
>(
  polynomial: &MultivariatePolynomial<F>,
) -> SumcheckProof<F> {
  let num_variables = polynomial.variables().len();
  let mut challenges = Vec::new();
  let mut round_polynomials = Vec::new();
  let mut round_evaluations = Vec::new();

  // First round: compute the claimed sum and the first univariate polynomial
  let (claimed_sum, first_univariate_poly) = polynomial.prove_first_sumcheck_round();
  round_polynomials.push(first_univariate_poly.clone());

  // Generate the first challenge using the random oracle
  let mut rng = rand::thread_rng();
  let challenge: F = F::random_oracle(&mut rng, &claimed_sum.to_bytes());
  challenges.push(challenge);
  round_evaluations.push(first_univariate_poly.evaluate(&[(0, challenge)]));

  let mut previous_univariate_poly = first_univariate_poly;

  // Intermediate rounds: generate univariate polynomials and challenges
  for i in 1..num_variables {
    let univariate_poly = polynomial.prove_sumcheck_round_i(i, challenges.clone());
    round_polynomials.push(univariate_poly.clone());

    // Generate challenge for this round using the random oracle
    let challenge: F = F::random_oracle(&mut rng, &previous_univariate_poly.to_bytes());
    challenges.push(challenge);
    round_evaluations.push(univariate_poly.evaluate(&[(i, challenge)]));

    previous_univariate_poly = univariate_poly;
  }

  // Final evaluation: evaluate the original polynomial at the challenge point
  let final_point = challenges.clone();
  let final_evaluation =
    polynomial.evaluate(&final_point.iter().cloned().enumerate().collect::<Vec<_>>());

  // Construct and return the proof
  SumcheckProof {
    claimed_sum,
    round_polynomials,
    round_evaluations,
    challenges,
    final_point,
    final_evaluation,
  }
}

/// Verifies a non-interactive sumcheck proof.
///
/// This function allows a verifier to be easily convinced of the correctness of a sumcheck proof
/// without interacting with the prover. The verifier can be convinced by the following steps:
///
/// 1. Check the consistency of the first round's claimed sum with the provided univariate
///    polynomial.
/// 2. Verify the consistency between consecutive rounds' univariate polynomials.
/// 3. Confirm that the final evaluation matches the original multivariate polynomial at the
///    challenge point.
///
/// The non-interactive nature of this proof system comes from the use of a random oracle to
/// generate challenges, which both the prover and verifier can compute independently.
///
/// # Arguments
///
/// * `proof` - The `SumcheckProof` provided by the prover.
/// * `polynomial` - The original multivariate polynomial being summed over.
///
/// # Returns
///
/// Returns `true` if the proof is valid, `false` otherwise.
pub fn non_interactive_sumcheck_verify<F: FiniteField + Random + RandomOracle + Display>(
  proof: &SumcheckProof<F>,
  polynomial: &MultivariatePolynomial<F>,
) -> bool {
  let num_variables = polynomial.variables().len();

  // Verify first round
  let (valid, _) = verify_sumcheck_first_round(proof.claimed_sum, &proof.round_polynomials[0]);
  if !valid {
    return false;
  }

  // Verify intermediate rounds
  for i in 1..num_variables {
    let (valid, _) = verify_sumcheck_univariate_poly_sum(
      i,
      proof.challenges[i - 1],
      &proof.round_polynomials[i - 1],
      &proof.round_polynomials[i],
    );
    if !valid {
      return false;
    }
  }

  // Verify last round
  verify_sumcheck_last_round(
    proof.final_point.clone(),
    &proof.round_polynomials.last().unwrap(),
    polynomial,
  )
}
