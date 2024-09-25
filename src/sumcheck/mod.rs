//! This module implements the sum-check protocol for multivariate polynomials over finite fields.
//!
//! ## Overview
//! The sum-check protocol is an interactive proof system where a prover convinces a verifier
//! of the sum of a multivariate polynomial over a boolean hypercube. The protocol proceeds
//! in rounds, reducing the number of variables in each round.
//!
//! - [`SumCheckProver`] represents the prover in the protocol.
//! - [`SumCheckVerifier`] represents the verifier in the protocol.
//! - [`SumCheck`] encapsulates both prover and verifier, managing the entire protocol.

use rand::thread_rng;

use super::*;
use crate::{algebra::field::FiniteField, multi_var_poly::MultiVarPolynomial};

/// Represents the prover in the sum-check protocol.
pub struct SumCheckProver<F: FiniteField> {
  /// The multivariate polynomial being summed over.
  pub multi_var_poly: MultiVarPolynomial<F>,
  /// Tracks the current round of the protocol.
  pub current_round:  usize,
  /// The total number of rounds in the protocol.
  pub total_rounds:   usize,
}

impl<F: FiniteField> SumCheckProver<F> {
  /// Creates a new SumCheckProver instance.
  ///
  /// ## Arguments:
  /// - `poly`: The multivariate polynomial to be used in the protocol.
  ///
  /// ## Returns:
  /// - A new `SumCheckProver` instance.
  pub fn new(poly: MultiVarPolynomial<F>) -> Self {
    let tot_rnds = poly.num_var();
    SumCheckProver { multi_var_poly: poly, current_round: 0, total_rounds: tot_rnds }
  }

  /// Computes the sum of the polynomial over the boolean hypercube.
  ///
  /// ## Returns:
  /// - The sum of the polynomial over the boolean hypercube.
  pub fn sum_poly(&self) -> F { self.multi_var_poly.sum_over_bool_hypercube() }

  /// Generates the univariate polynomial to be sent to the Verifier in the current round of the
  /// protocol.
  ///
  /// ## Returns:
  /// - A vector of field elements representing the coefficients of the univariate polynomial.
  pub fn send_poly(&self) -> Vec<F> {
    if self.multi_var_poly.num_var() > 1 {
      let tot_deg_ex_first: usize =
        self.multi_var_poly.degree.iter().skip(1).map(|&x| x + 1).product();

      let mut poly_to_send: Vec<F> = vec![];
      // need to include degree[0] in the loop here
      for i in 0..=self.multi_var_poly.degree[0] {
        let degree_ex_first = self.multi_var_poly.degree[1..].to_vec();
        let x_to_i_coeffs = self.multi_var_poly.coefficients
          [i * tot_deg_ex_first..(i + 1) * tot_deg_ex_first]
          .to_vec();
        // Over here we use the fact that if
        // $g(X_1, X_2, ..., X_n) = \sum_{i=0}^d c_i(X_2, X_3, ..., X_n) X^i$
        // then
        // $\sum_{X_2, ..., X_n \in \{0,1\}} g(X_1, X_2, ..., X_n) = \sum_{i=0}^d [\sum_{X_2, ...,
        // X_n \in \{0,1\}} c_i(X_2, X_3, ..., X_n)] X^i$
        // so the coefficients of the polynomial sent by the Prover are just the
        // `sum_over_bool_hypercube` for the MultiVarPolynomials given by coefficients
        // `x_to_i_coeffs` where the variables have degrees = `degree_ex_first`
        poly_to_send.push(
          MultiVarPolynomial::new(degree_ex_first, x_to_i_coeffs)
            .unwrap()
            .sum_over_bool_hypercube(),
        );
      }
      poly_to_send
    } else {
      self.multi_var_poly.coefficients.clone()
    }
  }

  /// Reduces the multivariate polynomial based on the verifier's challenge, that is, sets the
  /// variable in the first position equal to the challenge. Computes coefficients for the rest of
  /// the variables based on this and changes the `multi_var_poly` stored accordingly.
  ///
  /// ## Arguments:
  /// - `r`: The challenge field element from the verifier.
  pub fn reduce_poly(&mut self, r: F) {
    if self.multi_var_poly.num_var() > 1 {
      let tot_deg_ex_first: usize =
        self.multi_var_poly.degree.iter().skip(1).map(|&x| x + 1).product();

      // These clone the vectors
      let degree_ex_first = self.multi_var_poly.degree[1..].to_vec();
      let x_to_0_coeffs = self.multi_var_poly.coefficients[0..tot_deg_ex_first].to_vec();
      let mut new_multi_var_poly = MultiVarPolynomial::new(degree_ex_first, x_to_0_coeffs).unwrap();

      for i in 1..=self.multi_var_poly.degree[0] {
        let degree_ex_first = self.multi_var_poly.degree[1..].to_vec();
        let x_to_i_coeffs = self.multi_var_poly.coefficients
          [i * tot_deg_ex_first..(i + 1) * tot_deg_ex_first]
          .to_vec();

        // Similar to `send_poly` above if
        // $g(X_1, X_2, ..., X_n) = \sum_{i=0}^d c_i(X_2, X_3, ..., X_n) X^i$
        // then
        // $g(r, X_2, ..., X_n) = \sum_{i=0}^d c_i(X_2, X_3, ..., X_n) r^i$
        new_multi_var_poly +=
          MultiVarPolynomial::new(degree_ex_first, x_to_i_coeffs).unwrap() * r.pow(i);
      }

      self.multi_var_poly = new_multi_var_poly;
    } else {
      self.multi_var_poly =
        MultiVarPolynomial::new(vec![0], vec![self.multi_var_poly.evaluation(&[r])]).unwrap();
    }
    self.current_round += 1;
  }
}

/// Represents the verifier in the sum-check protocol.
pub struct SumCheckVerifier<F: FiniteField> {
  /// Tracks the current round of the sum-check protocol
  pub current_round:   usize,
  /// The total number of rounds in the protocol.
  pub total_rounds:    usize,
  /// Stores the degrees of the variables in the multivariate polynomial being summed over.
  pub degree:          Vec<usize>,
  /// Stores the result claimed by the Prover for the sum over the multivariate polynomial.
  pub result:          F,
  /// Tracks the value of polynomial sum claimed by the Prover in the present round. It is public
  /// only for debugging purposes.
  pub claim:           F,
  /// Vector storing challenges sent by the Verifier so far.
  pub challenges_sent: Vec<F>,
}
impl<F: FiniteField> SumCheckVerifier<F> {
  /// Creates a new `SumCheckVerifier` instance.
  ///
  /// ## Arguments:
  /// - `c`: The claimed sum of the polynomial.
  /// - `deg`: A vector representing the degrees of each variable in the polynomial.
  ///
  /// ## Returns:
  /// - A new `SumCheckVerifier` instance.
  pub fn new(c: F, deg: Vec<usize>) -> Self {
    Self {
      current_round:   0,
      total_rounds:    deg.len(),
      degree:          deg,
      result:          c,
      claim:           c,
      challenges_sent: vec![],
    }
  }

  /// Verifies the prover's polynomial for the current round and generates a challenge.
  ///
  /// ## Arguments:
  /// - `h_poly`: The univariate polynomial sent by the prover for this round.
  ///
  /// ## Returns:
  /// - The challenge field element for the next round.
  pub fn verify_internal_rounds(&mut self, h_poly: Vec<F>) -> F {
    assert_eq!(
      h_poly.len(),
      self.degree[self.current_round] + 1,
      "Verifier Abort: Prover's polynomial size incorrect!"
    );
    let h_poly_at_0 = h_poly[0];
    let mut h_poly_at_1 = F::ZERO;
    for item in h_poly.clone() {
      h_poly_at_1 += item;
    }
    let sum = h_poly_at_0 + h_poly_at_1;
    assert_eq!(
      sum, self.claim,
      "Verifier Abort: Prover's polynomial doesn't evaluate to claimed value"
    );

    let mut rng = thread_rng();
    let challenge = F::from(rng.gen::<usize>());

    // This is the value the Verifier will check against in the next round
    // new_claim = h_poly(challenge) as a univariate polynomial
    // we are implementing univariate polynomial evaluation here, since we can't use existing
    // [`Polynomial`] with variable size degree
    let mut new_claim = F::ZERO;
    for (i, coeff) in h_poly.iter().enumerate() {
      new_claim += *coeff * challenge.pow(i);
    }
    self.claim = new_claim;
    self.current_round += 1;
    self.challenges_sent.push(challenge);

    challenge
  }

  /// Verifies the final result of the protocol using the provided oracle.
  ///
  /// ## Arguments:
  /// - `oracle`: A function that checks if the claimed value of the evaluation of the multivariate
  ///   polynomial at the point given by `&challenges_sent:&Vec<F>` is correct or not. Using a
  ///   oracle like this should allow us to use both simple evaluation by the Verifier as well as a
  ///   commitment proof.
  pub fn verify_final_result(&self, oracle: impl Fn(&Vec<F>, F) -> bool) {
    assert!(
      oracle(&self.challenges_sent, self.claim),
      "Verifier Abort: Final value of polynomial claimed by the Prover is incorrect"
    );
  }
}

/// Represents the entire sum-check protocol, including both prover and verifier.
pub struct SumCheck<F: FiniteField> {
  /// The sum-check Prover object
  pub prover:         SumCheckProver<F>,
  /// The sum-check Verifier object
  pub verifier:       SumCheckVerifier<F>,
  /// The multivariate polynomial being summed over
  pub multi_var_poly: MultiVarPolynomial<F>,
  /// A flag which allows which prints the entire protocol if set to `true`
  pub verbose:        bool,
}
impl<F: FiniteField> SumCheck<F> {
  /// Creates a new SumCheck instance.
  ///
  /// ## Arguments:
  /// - `poly`: The multivariate polynomial to be used in the protocol.
  /// - `verbose`: A boolean flag indicating whether to output detailed protocol steps.
  ///
  /// ## Returns:
  /// - A new `SumCheck` instance.
  pub fn new(poly: MultiVarPolynomial<F>, verbose: bool) -> Self {
    let prover = SumCheckProver::new(poly.clone());
    let claimed_sum = prover.sum_poly();
    let verifier = SumCheckVerifier::new(claimed_sum, poly.degree.clone());
    Self { prover, verifier, multi_var_poly: poly, verbose }
  }

  /// Evaluates the multivariate polynomial at a given point.
  ///
  /// ## Arguments:
  /// - `r`: A vector of field elements representing the point of evaluation.
  /// - `claim`: The claimed value of the polynomial at the given point.
  ///
  /// ## Returns:
  /// - A boolean indicating whether the evaluation matches the claim.
  pub fn evaluation_oracle(&self, r: &[F], claim: F) -> bool {
    self.multi_var_poly.evaluation(r) == claim
  }

  /// Runs the interactive sum-check protocol between the prover and verifier.
  pub fn run_interactive_protocol(&mut self) {
    if self.verbose {
      println!("Starting Sum-Check Protocol");
      println!("Initial result claimed: {:?}", self.verifier.result);
    }
    for i in 0..self.multi_var_poly.num_var() {
      let rnd_poly = self.prover.send_poly();
      if self.verbose {
        println!("Round {}", i + 1);
        println!("P ----> V: {}", format_polynomial(&rnd_poly));
      }

      let challenge = self.verifier.verify_internal_rounds(rnd_poly);
      if self.verbose {
        println!("V ----> P: r_{} = {:?}", i + 1, challenge);
      }
      self.prover.reduce_poly(challenge);
    }
    if self.verbose {
      println!("Final verification:");
      println!("Challenges: {:?}", self.verifier.challenges_sent);
      println!("Claimed value at this point: {:?}", self.verifier.claim);
    }
    let oracle = |r: &Vec<F>, claim: F| self.evaluation_oracle(r, claim);
    self.verifier.verify_final_result(oracle);
    if self.verbose {
      println!("Protocol completed successfully");
    }
  }
}

/// Helper function to format a polynomial as a string.
///
/// ## Arguments:
/// - `coeffs`: A slice of field elements representing the coefficients of the polynomial.
///
/// ## Returns:
/// - A string representation of the polynomial.
fn format_polynomial<F: FiniteField>(coeffs: &[F]) -> String {
  let mut terms: Vec<String> = Vec::new();
  for (i, coeff) in coeffs.iter().enumerate() {
    if *coeff != F::ZERO {
      match i {
        0 => terms.push(format!("{:?}", coeff)),
        1 => terms.push(format!("{:?} X", coeff)),
        _ => terms.push(format!("{:?} X^{}", coeff, i)),
      }
    }
  }
  if terms.is_empty() {
    "0".to_string()
  } else {
    terms.join(" + ")
  }
}

#[cfg(test)] mod tests;
