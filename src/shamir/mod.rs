//! This module implements Shamir's Secret Sharing Scheme.
//!
//! Given a secret represented as a u128, the secret is split into a set
//! of shares such that any subset of shares of size at least `threshold` (k,n) where n = 2k-1
//! can reconstruct the secret using Lagrange interpolation over a finite field.
//!
//! The chosen finite field is GF(PRIME) with PRIME = 2^127 - 1. Be sure that the provided
//! secret is less than PRIME.

use rand::Rng;

/// Prime modulus for finite field arithmetic: 2^127 - 1.
const PRIME: u128 = 170141183460469231731687303715884105727;

/// A share is represented as a tuple (x, y) where both x and y are elements of GF(PRIME).
pub type Share = (u128, u128);

/// Splits the secret into `share_count` shares, any `threshold` of which are needed to reconstruct
/// the secret. The secret is assumed to be less than PRIME.
///
/// # Arguments
///
/// * `secret` - The secret to be shared (must be less than PRIME).
/// * `threshold` - Minimum number of shares required to reconstruct the secret.
/// * `share_count` - Total number of shares to generate.
///
/// # Panics
///
/// This function panics if `threshold` is 0, if `share_count` is less than `threshold`, or if the
/// secret is not less than PRIME.
///
/// # Returns
///
/// A vector of shares, where each share is a tuple (x, y).
pub fn split_secret(secret: u128, threshold: usize, share_count: usize) -> Vec<Share> {
  assert!(threshold > 0, "threshold must be at least 1");
  assert!(share_count >= threshold, "share count must be at least the threshold");
  assert!(secret < PRIME, "secret must be less than PRIME");

  // Generate random coefficients for the polynomial.
  // The polynomial has degree (threshold - 1) with a0 = secret.
  let mut rng = rand::thread_rng();
  let mut coeffs = vec![secret];
  for _ in 1..threshold {
    coeffs.push(rng.gen_range(0..PRIME));
  }

  // Evaluate polynomial at x = 1, 2, ... share_count.
  let mut shares = Vec::with_capacity(share_count);
  for i in 1..=share_count as u128 {
    let y = eval_poly(&coeffs, i);
    shares.push((i, y));
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
/// The reconstructed secret as a u128.
pub fn combine_shares(shares: &[Share]) -> u128 {
  assert!(!shares.is_empty(), "at least one share is required");

  let mut secret = 0u128;
  for (j, &(xj, yj)) in shares.iter().enumerate() {
    let mut numerator = 1u128;
    let mut denominator = 1u128;
    for (m, &(xm, _)) in shares.iter().enumerate() {
      if m == j {
        continue;
      }
      let term_numer = (PRIME + 0 - xm) % PRIME;
      numerator = mod_mul(numerator, term_numer, PRIME);
      let term_denom = (xj + PRIME - xm) % PRIME;
      denominator = mod_mul(denominator, term_denom, PRIME);
    }
    let inv = mod_inv(denominator, PRIME);
    let lagrange_coeff = mod_mul(numerator, inv, PRIME);
    secret = (secret + mod_mul(yj, lagrange_coeff, PRIME)) % PRIME;
  }
  secret
}

/// Evaluates the polynomial with the given coefficients at x.
/// Coefficients should be ordered such that coeffs[0] is the constant term.
/// All arithmetic is performed modulo PRIME using modular multiplication.
///
/// # Arguments
///
/// * `coeffs` - Slice of polynomial coefficients.
/// * `x` - The point at which to evaluate the polynomial.
///
/// # Returns
///
/// The evaluated value modulo PRIME.
fn eval_poly(coeffs: &[u128], x: u128) -> u128 {
  let mut result = 0u128;
  let mut power = 1u128;
  for &coeff in coeffs {
    result = (result + mod_mul(coeff, power, PRIME)) % PRIME;
    power = mod_mul(power, x, PRIME);
  }
  result
}

/// Computes the modular inverse of a modulo p using the Extended Euclidean Algorithm.
///
/// # Arguments
///
/// * `a` - The value for which to compute the inverse (must be nonzero and coprime to p).
/// * `p` - The prime modulus.
///
/// # Panics
///
/// Panics if the modular inverse does not exist (i.e. if `a` and `p` are not coprime).
fn mod_inv(a: u128, p: u128) -> u128 {
  // Convert a and p to i128 for computation. This is safe because PRIME < 2^127.
  let mut a = a as i128;
  let mut p = p as i128;
  let (mut t, mut newt) = (0i128, 1i128);
  let (mut r, mut newr) = (p, a);

  while newr != 0 {
    let quotient = r / newr;
    let temp_t = newt;
    newt = t - quotient * newt;
    t = temp_t;

    let temp_r = newr;
    newr = r - quotient * newr;
    r = temp_r;
  }

  if r != 1 {
    panic!("a is not invertible");
  }
  if t < 0 {
    t += p;
  }
  t as u128
}

/// Performs modular multiplication of two values `a` and `b` modulo `modulus`.
///
/// This routine uses an iterative doubling method to avoid overflow that can occur when directly
/// multiplying two u128 values.
///
/// # Arguments
///
/// * `a` - The first operand.
/// * `b` - The second operand.
/// * `modulus` - The modulus under which to perform the multiplication.
///
/// # Returns
///
/// The value of (a * b) % modulus.
fn mod_mul(a: u128, b: u128, modulus: u128) -> u128 {
  let mut result = 0u128;
  let mut a = a % modulus;
  let mut b = b;
  while b > 0 {
    if b & 1 == 1 {
      result = (result + a) % modulus;
    }
    a = (a << 1) % modulus;
    b >>= 1;
  }
  result
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_split_and_combine_single() {
    let secret = 123456789u128;
    let threshold = 3;
    let share_count = 5;
    let shares = split_secret(secret, threshold, share_count);

    // Reconstruct using exactly the threshold number of shares.
    let subset = &shares[..threshold];
    let recovered = combine_shares(subset);
    assert_eq!(secret, recovered);
  }

  #[test]
  fn test_split_and_combine_all() {
    let secret = 987654321u128;
    let threshold = 4;
    let share_count = 7;
    let shares = split_secret(secret, threshold, share_count);

    // Reconstruct using all shares.
    let recovered = combine_shares(&shares);
    assert_eq!(secret, recovered);
  }

  #[test]
  fn test_interpolation_properties() {
    // Ensure that different subsets of shares (with at least the threshold) can reconstruct the
    // secret.
    let secret = 42u128;
    let threshold = 3;
    let share_count = 6;
    let shares = split_secret(secret, threshold, share_count);

    // Test multiple combinations.
    for indices in vec![[0, 2, 4], [1, 3, 5], [0, 1, 2]] {
      let subset: Vec<Share> = indices.iter().map(|&i| shares[i]).collect();
      let recovered = combine_shares(&subset);
      assert_eq!(secret, recovered);
    }
  }
}
