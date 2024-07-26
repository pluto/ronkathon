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
/// RSAKey struct
pub struct RSA {
  /// pub key (e,n)
  pub private_key: PrivateKey,
  /// priv key (d,n)
  pub public_key:  PublicKey,
}

/// private key
pub struct PrivateKey {
  /// gcd(e, totient) = 1
  e: usize,
  /// modulus
  n: usize,
}

/// public key
pub struct PublicKey {
  /// d x e mod totient = 1
  d: usize,
  /// modulus
  n: usize,
}

impl RSA {
  /// Encrypts a message using the RSA algorithm
  #[allow(dead_code)]
  /// Encrypts a message using the RSA algorithm
  /// C = P^e mod n
  const fn encrypt(&self, message: u32) -> u32 {
    message.pow(self.private_key.e as u32) % self.private_key.n as u32
  }

  #[allow(dead_code)]
  /// Decrypts a cipher using the RSA algorithm
  /// P = C^d mod n
  const fn decrypt(&self, cipher: u32) -> u32 {
    cipher.pow(self.public_key.d as u32) % self.public_key.n as u32
  }
}
/// Key generation for the RSA algorithm
/// TODO: Implement a secure key generation algorithm using miller rabin primality test
pub fn rsa_key_gen(p: usize, q: usize) -> RSA {
  assert!(is_prime(p));
  assert!(is_prime(q));
  let n = p * q;
  let e = generate_e(p, q);
  let totient = euler_totient(p as u64, q as u64);
  let d = mod_inverse(e, totient);
  RSA { private_key: PrivateKey { e: e as usize, n }, public_key: PublicKey { d: d as usize, n } }
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

/// Generates a random prime number bigger than 1_000_000
pub fn random_prime(first_prime: usize) -> usize {
  let mut n = 1_000_000;
  while !is_prime(n) && n != first_prime {
    n += 1;
  }
  n
}

/// Primality testing in a constant function for compile time checks
pub const fn is_prime(n: usize) -> bool {
  if n <= 1 {
    return false;
  }
  let mut i = 2;
  while i * i <= n {
    if n % i == 0 {
      return false;
    }
    i += 1;
  }
  true
}

/// Euler totient: Ψ(x)
pub const fn euler_totient(prime_1: u64, prime_2: u64) -> u64 { (prime_1 - 1) * (prime_2 - 1) }

/// GCD of two numbers
pub const fn gcd(a: u64, b: u64) -> u64 {
  if b == 0 {
    a
  } else {
    gcd(b, a % b)
  }
}
