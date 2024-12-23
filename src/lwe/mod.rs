use rand::Rng;

use crate::algebra::field::{extension::GaloisField, prime::PrimeField, Field, FiniteField};

// Small parameters for testing
// const N: usize = 4; // Dimension (use larger like 256 in practice)
// const Q: u32 = 97; // Modulus (prime, use larger in practice)
const K: usize = 1; // Parameter for binomial sampling

#[derive(Debug, Clone)]
pub struct PublicKey<const Q: usize, const N: usize> {
  a: [[PrimeField<Q>; N]; N], // Matrix A in Z_q^{n×n}
  b: [PrimeField<Q>; N],      // Vector b = As + e
}

#[derive(Debug, Clone)]
pub struct SecretKey<const Q: usize, const N: usize> {
  s: [PrimeField<Q>; N], // Secret vector in Z_q^n
}

#[derive(Debug, Clone)]
pub struct Ciphertext<const Q: usize> {
  u: Vec<PrimeField<Q>>, // First component
  v: PrimeField<Q>,      // Second component
}

fn sample_binomial<const Q: usize>() -> PrimeField<Q> {
  let mut rng = rand::thread_rng();
  let mut sum = PrimeField::<Q>::ZERO;

  for _ in 0..K {
    // Add 1 or 0 for first term
    if rng.gen::<bool>() {
      sum = sum + PrimeField::<Q>::ONE;
    }
    // Subtract 1 or 0 for second term
    if rng.gen::<bool>() {
      sum = sum - PrimeField::<Q>::ONE;
    }
  }
  sum
}

pub fn keygen<const Q: usize, const N: usize>() -> (PublicKey<Q, N>, SecretKey<Q, N>) {
  let mut rng = rand::thread_rng();

  // Generate random matrix A
  let mut a = [[PrimeField::<Q>::ZERO; N]; N];
  for i in 0..N {
    for j in 0..N {
      a[i][j] = PrimeField::from(rng.gen_range(0..Q));
    }
  }

  // Sample secret vector s with small coefficients
  let mut s = [PrimeField::<Q>::ZERO; N];
  for i in 0..N {
    s[i] = sample_binomial();
  }

  // Generate error vector e
  let mut e = [PrimeField::<Q>::ZERO; N];
  for i in 0..N {
    e[i] = sample_binomial();
  }

  // Compute b = As + e
  let mut b = [PrimeField::<Q>::ZERO; N];
  for i in 0..N {
    let mut sum = PrimeField::<Q>::ZERO;
    for j in 0..N {
      sum += a[i][j] * s[j];
    }
    sum += e[i];
    b[i] = sum;
  }

  (PublicKey { a, b }, SecretKey { s })
}

// TODO: Should impl the `SymmetricEncryption` trait
pub fn encrypt(pk: &PublicKey, message: bool) -> Ciphertext {
  let mut rng = rand::thread_rng();

  // Sample random vector r
  let mut r = vec![0; N];
  for i in 0..N {
    r[i] = rng.gen_range(0..2) as u32; // Binary vector
  }

  // Compute u = A^T r
  let mut u = vec![0; N];
  for i in 0..N {
    let mut sum = 0i32;
    for j in 0..N {
      sum += (pk.a[j][i] * r[j]) as i32;
    }
    u[i] = mod_q(sum);
  }

  // Compute v = b^T r + ⌊q/2⌋m
  let mut v = 0i32;
  for i in 0..N {
    v += (pk.b[i] * r[i]) as i32;
  }
  if message {
    v += (Q / 2) as i32;
  }

  Ciphertext { u, v: mod_q(v) }
}

pub fn decrypt(sk: &SecretKey, ct: &Ciphertext) -> bool {
  // Compute v - s^T u
  let mut sum = ct.v as i32;
  for i in 0..N {
    sum -= (sk.s[i] * ct.u[i]) as i32;
  }
  sum = mod_q(sum) as i32;

  // Check if closer to 0 or ⌊q/2⌋
  let q_half = (Q / 2) as i32;
  let mut dist_to_zero = sum.min(Q as i32 - sum);
  let mut dist_to_q_half = ((sum - q_half).abs()).min((sum - q_half + Q as i32).abs());

  dist_to_q_half < dist_to_zero
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_encryption_decryption() {
    // Test multiple random instances
    for _ in 0..100 {
      let (pk, sk) = keygen();

      // Test encryption and decryption of 0
      let ct_zero = encrypt(&pk, false);
      assert_eq!(decrypt(&sk, &ct_zero), false);

      // Test encryption and decryption of 1
      let ct_one = encrypt(&pk, true);
      assert_eq!(decrypt(&sk, &ct_one), true);
    }
  }

  #[test]
  fn test_with_fixed_randomness() {
    // This test would need a deterministic RNG to be meaningful
    // In practice, you'd want to test with known test vectors
  }

  #[test]
  fn test_binomial_distribution() {
    let mut counts = vec![0; 3]; // -1, 0, 1 for k=1
    for _ in 0..1000 {
      let sample = sample_binomial();
      counts[(sample + 1) as usize] += 1;
    }
    // Check rough distribution - should be approximately 1/4, 1/2, 1/4
    for count in counts.iter() {
      assert!(*count > 150); // Should be roughly 250 but allow some variance
    }
  }
}
