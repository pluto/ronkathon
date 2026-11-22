//! Primality testing with the Miller-Rabin test, and generation of random primes.
//!
//! - [`is_prime`]: deterministic for every [`u64`], by testing a fixed set of bases.
//! - [`miller_rabin`]: the probabilistic test with random bases, for a chosen number of rounds.
//! - [`random_prime`]: a random prime with an exact number of bits.
use rand::Rng;

/// Bases for which Miller-Rabin gives the right answer for every `n < 2^64`. See
/// [Jaeschke (1993)](https://doi.org/10.1090/S0025-5718-1993-1192971-8) and the
/// [primality test notes](https://miller-rabin.appspot.com/) for the bound.
const DETERMINISTIC_BASES: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

/// Computes `base^exponent mod modulus`, using `u128` so the products of two values below
/// `modulus` don't overflow.
pub fn mod_pow(base: u64, mut exponent: u64, modulus: u64) -> u64 {
  if modulus == 1 {
    return 0;
  }
  let modulus = modulus as u128;
  let mut base = base as u128 % modulus;
  let mut result = 1_u128;
  while exponent > 0 {
    if exponent & 1 == 1 {
      result = result * base % modulus;
    }
    base = base * base % modulus;
    exponent >>= 1;
  }
  result as u64
}

/// Writes `n - 1 = d · 2^s` with `d` odd. `n` must be odd and at least 3.
fn decompose(n: u64) -> (u64, u32) {
  let s = (n - 1).trailing_zeros();
  ((n - 1) >> s, s)
}

/// One round of Miller-Rabin: returns `false` if `a` proves that the odd number `n` is composite,
/// and `true` if `n` passes for this base (it is then prime, or `a` is a strong liar for `n`).
///
/// For a prime `n`, `a^d` is either 1, or squaring it repeatedly reaches `n - 1` before reaching 1,
/// since the only square roots of 1 modulo a prime are 1 and -1.
fn passes_round(n: u64, d: u64, s: u32, a: u64) -> bool {
  let mut x = mod_pow(a, d, n);
  if x == 1 || x == n - 1 {
    return true;
  }
  for _ in 1..s {
    x = ((x as u128 * x as u128) % n as u128) as u64;
    if x == n - 1 {
      return true;
    }
  }
  false
}

/// Handles `n < 4` and even numbers, which the rounds don't cover.
fn small_or_even(n: u64) -> Option<bool> {
  match n {
    0 | 1 => Some(false),
    2 | 3 => Some(true),
    _ if n % 2 == 0 => Some(false),
    _ => None,
  }
}

/// Returns whether `n` is prime. Deterministic: tests the bases in [`DETERMINISTIC_BASES`], which
/// is enough for every `u64`.
///
/// ## Example
/// ```
/// use ronkathon::primality::is_prime;
///
/// assert!(is_prime(101));
/// assert!(!is_prime(561)); // a Carmichael number, which fools the Fermat test
/// assert!(is_prime(18_446_744_073_709_551_557)); // the largest prime below 2^64
/// ```
pub fn is_prime(n: u64) -> bool {
  if let Some(answer) = small_or_even(n) {
    return answer;
  }
  let (d, s) = decompose(n);
  DETERMINISTIC_BASES.iter().all(|&a| a % n == 0 || passes_round(n, d, s, a))
}

/// The probabilistic Miller-Rabin test with `rounds` random bases.
///
/// Never rejects a prime. A composite number passes a single round for at most a quarter of the
/// bases, so it passes all rounds with probability at most `4^-rounds`.
pub fn miller_rabin<R: Rng + ?Sized>(n: u64, rounds: usize, rng: &mut R) -> bool {
  if let Some(answer) = small_or_even(n) {
    return answer;
  }
  let (d, s) = decompose(n);
  (0..rounds).all(|_| passes_round(n, d, s, rng.gen_range(2..n - 1)))
}

/// Returns a random prime with exactly `bits` bits, i.e. in `[2^(bits-1), 2^bits)`.
///
/// Draws random odd numbers with the top bit set until one is prime. By the prime number theorem
/// about one in `ln(2^bits) / 2` odd numbers of that size is prime, so this takes few tries.
///
/// ## Panics
/// If `bits` is not between 2 and 64.
pub fn random_prime<R: Rng + ?Sized>(bits: u32, rng: &mut R) -> u64 {
  assert!((2..=64).contains(&bits), "bits must be between 2 and 64");
  if bits == 2 {
    return rng.gen_range(2..=3);
  }
  let top_bit = 1_u64 << (bits - 1);
  let mask = if bits == 64 { u64::MAX } else { (1_u64 << bits) - 1 };
  loop {
    let candidate = (rng.gen::<u64>() & mask) | top_bit | 1;
    if is_prime(candidate) {
      return candidate;
    }
  }
}

#[cfg(test)]
mod tests {
  use rand::thread_rng;

  use super::*;

  /// Trial division, to compare against.
  fn is_prime_slow(n: u64) -> bool {
    n >= 2 && (2..).take_while(|i| i * i <= n).all(|i| n % i != 0)
  }

  #[test]
  fn matches_trial_division() {
    let mut rng = thread_rng();
    for n in 0..20_000 {
      assert_eq!(is_prime(n), is_prime_slow(n), "{n}");
      assert_eq!(miller_rabin(n, 20, &mut rng), is_prime_slow(n), "{n}");
    }
  }

  /// Carmichael numbers pass the Fermat test for every base coprime to them, but not
  /// Miller-Rabin.
  #[test]
  fn carmichael_numbers_are_composite() {
    for n in [561, 1105, 1729, 2465, 2821, 6601, 8911, 41041, 825_265, 321_197_185] {
      assert!(!is_prime(n), "{n}");
    }
  }

  /// Strong pseudoprimes to several of the first prime bases at once, which a smaller fixed set
  /// of bases would get wrong.
  #[test]
  fn strong_pseudoprimes_are_composite() {
    for n in
      [2047, 1_373_653, 25_326_001, 3_215_031_751, 2_152_302_898_747, 3_825_123_056_546_413_051]
    {
      assert!(!is_prime(n), "{n}");
    }
  }

  #[test]
  fn large_primes_and_composites() {
    let largest_prime = 18_446_744_073_709_551_557; // largest prime below 2^64
    assert!(is_prime(largest_prime));
    assert!(is_prime((1 << 61) - 1)); // Mersenne prime
    assert!(!is_prime(u64::MAX));
    assert!(!is_prime(4_294_967_291 * 4_294_967_279)); // product of the two largest 32 bit primes
    assert!(miller_rabin(largest_prime, 20, &mut thread_rng()));
  }

  #[test]
  fn mod_pow_matches_naive() {
    for (base, exponent, modulus) in
      [(2, 10, 1000), (3, 0, 7), (5, 3, 1), (7, 13, 101), (u64::MAX, 2, 97)]
    {
      let expected =
        (0..exponent).fold(1_u128, |acc, _| acc * base as u128 % modulus as u128) % modulus as u128;
      assert_eq!(mod_pow(base, exponent, modulus) as u128, expected);
    }
  }

  #[test]
  fn random_prime_has_requested_bits() {
    let mut rng = thread_rng();
    for bits in [2, 3, 8, 16, 32, 63, 64] {
      let prime = random_prime(bits, &mut rng);
      assert!(is_prime(prime), "{prime}");
      assert_eq!(64 - prime.leading_zeros(), bits, "{prime} should have {bits} bits");
    }
  }
}
