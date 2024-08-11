use rand::thread_rng;

use super::*;
use crate::{algebra::field::FiniteField, multi_var_poly::MultiVarPolynomial};

pub struct SumCheckProver<F: FiniteField> {
  pub multi_var_poly: MultiVarPolynomial<F>,
  pub current_round:  usize,
  pub total_rounds:   usize,
}

impl<F: FiniteField> SumCheckProver<F> {
  pub fn new(poly: MultiVarPolynomial<F>) -> Self {
    let tot_rnds = poly.num_var();
    SumCheckProver { multi_var_poly: poly, current_round: 0, total_rounds: tot_rnds }
  }

  pub fn sum_poly(&self) -> F { return self.multi_var_poly.sum_over_bool_hypercube(); }

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
      return poly_to_send;
    } else {
      return self.multi_var_poly.coefficients.clone();
    }
  }

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
        MultiVarPolynomial::new(vec![0], vec![self.multi_var_poly.evaluation(&vec![r])]).unwrap();
    }
    self.current_round += 1;
  }
}

pub struct SumCheckVerifier<F: FiniteField> {
  pub current_round:   usize,
  pub total_rounds:    usize,
  pub degree:          Vec<usize>,
  pub result:          F,
  pub claim:           F,
  pub challenges_sent: Vec<F>,
  pub _poly_received:  Vec<Vec<F>>,
}
impl<F: FiniteField> SumCheckVerifier<F> {
  fn new(c: F, deg: Vec<usize>) -> Self {
    Self {
      current_round:   0,
      total_rounds:    deg.len(),
      degree:          deg,
      result:          c,
      claim:           c,
      challenges_sent: vec![],
      _poly_received:  vec![],
    }
  }

  fn verify_internal_rounds(&mut self, h_poly: Vec<F>) -> F {
    assert_eq!(
      h_poly.len(),
      self.degree[self.current_round] + 1,
      "Verifier Abort: Prover's polynomial size incorrect!"
    );
    let h_poly_at_0 = h_poly[0];
    let mut h_poly_at_1 = F::ZERO;
    for i in 0..h_poly.len() {
      h_poly_at_1 += h_poly[i];
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
    for i in 0..h_poly.len() {
      new_claim += h_poly[i] * challenge.pow(i);
    }
    self.claim = new_claim;
    self.current_round += 1;
    self.challenges_sent.push(challenge);
    self._poly_received.push(h_poly);

    return challenge;
  }

  fn verify_final_result(&self, oracle: impl Fn(&Vec<F>, F) -> bool) {
    assert!(
      oracle(&self.challenges_sent, self.claim),
      "Verifier Abort: Final value of polynomial claimed by the Prover is incorrect"
    );
  }
}

pub struct SumCheck<F: FiniteField> {
  pub prover:         SumCheckProver<F>,
  pub verifier:       SumCheckVerifier<F>,
  pub multi_var_poly: MultiVarPolynomial<F>,
  pub verbose:        bool,
}
impl<F: FiniteField> SumCheck<F> {
  fn new(poly: MultiVarPolynomial<F>, verbose: bool) -> Self {
    let prover = SumCheckProver::new(poly.clone());
    let claimed_sum = prover.sum_poly();
    let verifier = SumCheckVerifier::new(claimed_sum, poly.degree.clone());
    Self { prover, verifier, multi_var_poly: poly, verbose }
  }

  pub fn evaluation_oracle(&self, r: &Vec<F>, claim: F) -> bool {
    return self.multi_var_poly.evaluation(r) == claim;
  }

  pub fn run_interactive_protocol(&mut self) {
    if self.verbose {
      println!("Starting Sum-Check Protocol");
      println!("Initial claim: {:?}", self.verifier.claim);
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
