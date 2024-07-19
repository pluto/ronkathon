//! Tiny RSA implementation
//! TinyRSA module for educational cryptographic implementations.
//! RSA Security Assumptions:
//! - The security of RSA relies on the difficulty of factoring large integers.
//! - The implementation is secure if the modulus is the product of two large random primes (they
//!   are not random or big in these tests).
//! - The size of the modulus should be at least 2048 bits.
#![doc = include_str!("./README.md")]
#[cfg(test)] mod tests;

#[allow(dead_code)]
/// Computes the modular inverse of e mod totient
const fn mod_inverse(e: u64, totient: u64) -> u64 {
  let mut d = 1;
  while (d * e) % totient != 1 {
    d += 1;
  }
  d
}

/// private key
pub struct PrivateKey {
  /// d x e mod totient = 1
  d:     usize,
  /// modulus
  pub n: usize,
}

/// public key
pub struct PublicKey {
  /// gcd(e, totient) = 1
  e:     usize,
  /// modulus
  pub n: usize,
}

/// RSA encryption
pub struct RSAEncryption {
  /// RSA public key
  pub public_key: PublicKey,
}

/// RSA decryption
pub struct RSADecryption {
  /// RSA private key
  pub private_key: PrivateKey,
}

impl RSAEncryption {
  /// Encrypts a message using the RSA algorithm
  /// C = P^e mod n
  pub const fn encrypt(&self, plaintext: u32) -> u32 {
    let mut plaintext = plaintext;
    let mut res = 1;
    let mut exp = self.public_key.e as u32;

    while exp > 0 {
      if exp % 2 == 1 {
        res = ((res as u64 * plaintext as u64) % self.public_key.n as u64) as u32;
      }
      plaintext = ((plaintext as u64).pow(2) % self.public_key.n as u64) as u32;
      exp >>= 1;
    }

    res
  }
}

impl RSADecryption {
  /// Decrypts a cipher using the RSA algorithm
  /// P = C^d mod n
  pub const fn decrypt(&self, ciphertext: u32) -> u32 {
    let mut res = 1;
    let mut ciphertext = ciphertext;
    let mut exp = self.private_key.d as u32;

    while exp > 0 {
      if exp % 2 == 1 {
        res = ((res as u64 * ciphertext as u64) % self.private_key.n as u64) as u32;
      }
      ciphertext = ((ciphertext as u64).pow(2) % self.private_key.n as u64) as u32;
      exp >>= 1;
    }

    res
    // ((ciphertext as u64).pow(self.private_key.d as u32) % self.private_key.n as u64) as u32
  }
}

/// Key generation for the RSA algorithm
/// TODO: Implement a secure key generation algorithm using miller rabin primality test
pub fn rsa_key_gen(p: usize, q: usize) -> (RSAEncryption, RSADecryption) {
  assert!(is_prime(p));
  assert!(is_prime(q));
  let n = p * q;
  let e = generate_e(p, q);
  let totient = euler_totient(p as u64, q as u64);
  let d = mod_inverse(e, totient);
  (RSAEncryption { public_key: PublicKey { e: e as usize, n } }, RSADecryption {
    private_key: PrivateKey { d: d as usize, n },
  })
}

/// Generates e value for the RSA algorithm
/// gcd of totient and e must be 1 which is equivalent to: e and totient must be coprime
#[allow(dead_code)]
const fn generate_e(p: usize, q: usize) -> u64 {
  assert!(p > 1 && q > 2, "P and Q must be greater than 1");
  let totient = euler_totient(p as u64, q as u64);
  let mut e = 2;
  while e < totient {
    if gcd(totient, e) == 1 {
      // This check ensures e and totient are coprime
      return e;
    }
    e += 1;
  }
  panic!("Failed to find coprime e; totient should be greater than 1")
}

/// Generates a random prime number bigger than `begin`
pub fn random_prime(begin: usize) -> usize {
  let mut n = begin;
  while !is_prime(n) {
    n += 1;
  }
  n
}

fn is_prime(n: usize) -> bool {
  if n <= 1 {
    return false;
  }
  for i in 2..=((n as f64).sqrt() as usize) {
    if n % i == 0 {
      return false;
    }
  }
  true
}

const fn euler_totient(prime_1: u64, prime_2: u64) -> u64 { (prime_1 - 1) * (prime_2 - 1) }

const fn gcd(a: u64, b: u64) -> u64 {
  if b == 0 {
    a
  } else {
    gcd(b, a % b)
  }
}
