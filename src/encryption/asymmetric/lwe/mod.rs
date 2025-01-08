//! This module implements the Learning With Errors (LWE) public-key encryption scheme.
//!
//! LWE is a lattice-based cryptosystem whose security is based on the hardness of the
//! Learning With Errors problem, first introduced by Regev in 2005. The scheme encrypts
//! single bits and provides security against quantum computers.
//!
//! The implementation uses three type parameters:
//! - Q: The modulus (must be prime)
//! - N: The dimension of the lattice
//! - K: The parameter for the binomial distribution used for error sampling

use rand::Rng;

use super::AsymmetricEncryption;
use crate::algebra::field::{prime::PrimeField, Field};

/// An implementation of Learning With Errors (LWE) encryption
pub struct LWE<const Q: usize, const N: usize, const K: usize> {
  private_key: PrivateKey<Q, N>,
  public_key:  PublicKey<Q, N>,
}

/// The public key consisting of a random matrix A and vector b = As + e
#[derive(Debug, Clone)]
pub struct PublicKey<const Q: usize, const N: usize> {
  /// Random matrix in Z_q^{n×n}
  a: [[PrimeField<Q>; N]; N],
  /// Vector b = As + e where s is secret and e is error
  b: [PrimeField<Q>; N],
}

/// The private key consisting of the secret vector s
#[derive(Debug, Clone)]
pub struct PrivateKey<const Q: usize, const N: usize> {
  /// Secret vector with small coefficients
  s: [PrimeField<Q>; N],
}

/// A ciphertext consisting of vector u and scalar v
#[derive(Debug, Clone)]
pub struct Ciphertext<const Q: usize, const N: usize> {
  /// First component u = A^T r
  u: [PrimeField<Q>; N],
  /// Second component v = b^T r + ⌊q/2⌋m
  v: PrimeField<Q>,
}

/// Sample from a centered binomial distribution with parameter K
///
/// Returns a value in the range [-K, K] following a discrete approximation
/// of a Gaussian distribution.
pub fn sample_binomial<const Q: usize, const K: usize>() -> PrimeField<Q> {
  let mut rng = rand::thread_rng();
  let mut sum = PrimeField::<Q>::ZERO;

  for _ in 0..K {
    if rng.gen::<bool>() {
      sum += PrimeField::<Q>::ONE;
    }
    if rng.gen::<bool>() {
      sum -= PrimeField::<Q>::ONE;
    }
  }
  sum
}

impl<const Q: usize, const N: usize, const K: usize> LWE<Q, N, K> {
  pub fn new() -> LWE<Q, N, K> {
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
      s[i] = sample_binomial::<Q, K>();
    }

    // Generate error vector e
    let mut e = [PrimeField::<Q>::ZERO; N];
    for i in 0..N {
      e[i] = sample_binomial::<Q, K>();
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

    Self { public_key: PublicKey { a, b }, private_key: PrivateKey { s } }
  }
}

impl<const Q: usize, const N: usize, const K: usize> AsymmetricEncryption for LWE<Q, N, K> {
  type Ciphertext = Ciphertext<Q, N>;
  type Plaintext = bool;
  type PrivateKey = PrivateKey<Q, N>;
  type PublicKey = PublicKey<Q, N>;

  fn encrypt(&self, plaintext: &Self::Plaintext) -> Self::Ciphertext {
    let mut rng = rand::thread_rng();

    // Sample random vector r (binary)
    let mut r = [PrimeField::<Q>::ZERO; N];
    for i in 0..N {
      r[i] = PrimeField::from(rng.gen_range(0..2));
    }

    // Compute u = A^T r
    let mut u = [PrimeField::<Q>::ZERO; N];
    for i in 0..N {
      for j in 0..N {
        u[i] += self.public_key.a[j][i] * r[j];
      }
    }

    // Compute v = b^T r + ⌊q/2⌋m
    let mut v = PrimeField::<Q>::ZERO;
    for i in 0..N {
      v += self.public_key.b[i] * r[i];
    }

    if *plaintext {
      v += PrimeField::from(Q / 2);
    }

    Ciphertext { u, v }
  }

  fn decrypt(&self, ct: &Self::Ciphertext) -> Self::Plaintext {
    // Compute v - s^T u
    let mut result = ct.v;
    for i in 0..N {
      result -= self.private_key.s[i] * ct.u[i];
    }

    // Get q/2 as a field element
    let q_half = PrimeField::<Q>::from(Q / 2);

    // For distance to zero, we need min(x, q-x)
    let dist_to_zero = result.min(-result);

    // For distance to q/2, we need min(|x - q/2|, |q/2 - x|)
    let dist_to_q_half = if result >= q_half {
      // If result ≥ q/2, distance is min(result - q/2, q - result + q/2)
      (result - q_half).min(-result + q_half)
    } else {
      // If result < q/2, distance is min(q/2 - result, result + q/2)
      (q_half - result).min(result + q_half)
    };

    dist_to_q_half < dist_to_zero
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_encryption_decryption() {
    for _ in 0..100 {
      let lwe = LWE::<97, 4, 2>::new();

      // Test encryption and decryption of 0
      let ct_zero = lwe.encrypt(&false);
      assert_eq!(lwe.decrypt(&ct_zero), false, "Failed decrypting 0");

      // Test encryption and decryption of 1
      let ct_one = lwe.encrypt(&true);
      assert_eq!(lwe.decrypt(&ct_one), true, "Failed decrypting 1");
    }
  }
}
