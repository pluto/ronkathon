//! This module implements Shamir's Secret Sharing Scheme.
//!
//! Given a secret represented as a field element, the secret is split into a set
//! of shares such that any subset of shares of size at least `threshold` (k,n) where n = 2k-1
//! can reconstruct the secret using Lagrange interpolation over a finite field.
//!
//! The implementation is generic over any field that implements the `FiniteField` trait.

use rand::Rng;

use super::algebra::field::FiniteField;
use crate::polynomial::*;

/// A share is represented as a tuple (x, y) where both x and y are elements of the field F.
pub type Share<F> = (F, F);

/// Splits the secret into `share_count` shares, any `threshold` of which are needed to reconstruct
/// the secret.
///
/// # Arguments
///
/// * `secret` - The secret to be shared as a field element.
/// * `threshold` - Minimum number of shares required to reconstruct the secret.
/// * `share_count` - Total number of shares to generate.
///
/// # Panics
///
/// This function panics if `threshold` is 0 or if `share_count` is less than `threshold`.
///
/// # Returns
///
/// A vector of shares, where each share is a tuple (x, y).
pub fn split_secret<F: FiniteField, const THRESHOLD: usize>(
  secret: F,
  share_count: usize,
) -> Vec<Share<F>> {
  assert!(THRESHOLD > 0, "threshold must be at least 1");
  assert!(share_count >= THRESHOLD, "share count must be at least the threshold");

  // Generate random coefficients for the polynomial.
  // The polynomial has degree (THRESHOLD - 1) with a0 = secret.
  let mut rng = rand::thread_rng();
  let mut coeffs = Vec::with_capacity(THRESHOLD);
  coeffs.push(secret);
  for _ in 1..THRESHOLD {
    // Generate a random coefficient
    let mut random_value: usize = rng.gen();
    random_value %= F::ORDER;
    coeffs.push(F::from(random_value));
  }

  // Create polynomial once and evaluate it for each share.
  let p = Polynomial::<Monomial, F, { THRESHOLD }>::new(coeffs.try_into().unwrap());
  let mut shares = Vec::with_capacity(share_count);
  for i in 1..=share_count {
    let y = p.evaluate(F::from(i));
    shares.push((F::from(i), y));
  }
  shares
}

/// Reconstructs the secret from a list of shares using Lagrange interpolation.
///
/// # Arguments
///
/// * `shares` - A slice of shares (x, y) used to reconstruct the secret. The length of `shares`
///   should be at least the original threshold.
///
/// # Panics
///
/// This function panics if no shares are provided or if a modular inverse does not exist.
///
/// # Returns
///
/// The reconstructed secret as a field element.
pub fn combine_shares<F: FiniteField>(shares: &[Share<F>]) -> F {
  assert!(!shares.is_empty(), "at least one share is required");

  let mut secret = F::ZERO;
  for (j, &(xj, yj)) in shares.iter().enumerate() {
    let mut numerator = F::ONE;
    let mut denominator = F::ONE;
    for (m, &(xm, _)) in shares.iter().enumerate() {
      if m == j {
        continue;
      }
      let term_numer = F::ZERO - xm;
      numerator *= term_numer;
      let term_denom = xj - xm;
      denominator *= term_denom;
    }
    let inv = denominator.inverse().expect("denominator is not invertible");
    let lagrange_coeff = numerator * inv;
    secret += yj * lagrange_coeff;
  }
  secret
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::algebra::field::prime::PlutoBaseField;

  #[test]
  fn test_split_and_combine_single() {
    let secret = PlutoBaseField::new(12);
    let share_count = 5;
    let shares = split_secret::<PlutoBaseField, 3>(secret, share_count);

    // Reconstruct using exactly the threshold number of shares.
    let subset = &shares[..3];
    let recovered = combine_shares(subset);
    assert_eq!(secret, recovered);
  }

  #[test]
  fn test_split_and_combine_all() {
    let secret = PlutoBaseField::new(98);
    let share_count = 7;
    let shares = split_secret::<PlutoBaseField, 4>(secret, share_count);

    // Reconstruct using all shares.
    let recovered = combine_shares(&shares);
    assert_eq!(secret, recovered);
  }

  #[test]
  fn test_interpolation_properties() {
    // Ensure that different subsets of shares (with at least the threshold) can reconstruct the
    // secret.
    let secret = PlutoBaseField::new(42);
    let share_count = 6;
    let shares = split_secret::<PlutoBaseField, 3>(secret, share_count);

    // Test multiple combinations.
    for indices in vec![[0, 2, 4], [1, 3, 5], [0, 1, 2]] {
      let subset: Vec<Share<PlutoBaseField>> = indices.iter().map(|&i| shares[i]).collect();
      let recovered = combine_shares(&subset);
      assert_eq!(secret, recovered);
    }
  }
}
