//! Tiny RSA implementation
//! TinyRSA module for educational cryptographic implementations.
//! RSA Security Assumptions:
//! - The security of RSA relies on the difficulty of factoring large integers.
//! - The implementation is secure if the modulus is the product of two large random primes (they
//!   are not random or big in these tests).
//! - The size of the modulus should be at least 2048 bits.
use std::{
  iter::{Product, Sum},
  ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign},
};

pub mod arithmetic;
#[cfg(test)] mod tests;

use crate::field::FiniteField;

/// A field element for RSA operations with a modulus of P.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Default, PartialOrd)]
pub struct RSAField<const N: usize> {
  /// The value of the field element
  pub value: usize,
}

/// Constructs a new RSAField element
impl<const N: usize> RSAField<N> {
  /// Constructs a new RSAField element
  pub fn new(value: usize) -> Self {
    let p = random_prime(2);
    let q = random_prime(p);
    assert_ne!(p, q);
    Self { value: value % (p * q) }
  }
}

impl<const N: usize> FiniteField for RSAField<N> {
  const ONE: Self = Self { value: 1 };
  const ORDER: usize = N;
  // placeholder, fields without prime order don't have a primitive element
  const PRIMITIVE_ELEMENT: Self = Self::ONE;
  const ZERO: Self = Self { value: 0 };

  fn inverse(&self) -> Option<Self> {
    if self.value == 0 {
      return None;
    }
    let exponent = Self::ORDER - 2;
    let mut result = Self::ONE;
    let mut base = *self;
    let mut power = exponent;

    while power > 0 {
      if power & 1 == 1 {
        result *= base;
      }
      base = base * base;
      power >>= 1;
    }
    Some(result)
  }

  fn pow(self, power: usize) -> Self {
    if power == 0 {
      Self::ONE
    } else if power == 1 {
      self
    } else if power % 2 == 0 {
      Self::new((self.pow(power / 2).value * self.pow(power / 2).value) % Self::ORDER)
    } else {
      Self::new((self.pow(power / 2).value * self.pow(power / 2).value * self.value) % Self::ORDER)
    }
  }
}

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
pub struct RSAKey {
  /// field size
  pub n:           usize,
  /// pub key (e,n)
  pub private_key: (usize, usize),
  /// priv key (d,n)
  pub public_key:  (usize, usize),
}

impl RSAKey {
  /// Encrypts a message using the RSA algorithm
  #[allow(dead_code)]
  /// Encrypts a message using the RSA algorithm
  const fn encrypt(&self, message: u32) -> u32 {
    message.pow(self.private_key.0 as u32) % self.n as u32
  }

  #[allow(dead_code)]
  /// Decrypts a cipher using the RSA algorithm
  const fn decrypt(&self, cipher: u32) -> u32 {
    cipher.pow(self.public_key.0 as u32) % self.n as u32
  }
}
/// Key generation for the RSA algorithm
/// TODO: Implement a secure key generation algorithm using miller rabin primality test
pub fn rsa_key_gen() -> RSAKey {
  let p = 3;
  let q = 5;
  let n = p * q;
  let e = generate_e(p, q);
  let totient = euler_totient(p as u64, q as u64);
  let d = mod_inverse(e, totient);
  RSAKey { n, private_key: (e as usize, n), public_key: (d as usize, n) }
}

/// Generates e value for the RSA algorithm
#[allow(dead_code)]
const fn generate_e(p: usize, q: usize) -> u64 {
  assert!(p > 1 && q > 2, "P and Q must be greater than 1");
  let totient = euler_totient(p as u64, q as u64);
  let mut e = 2;
  while e < totient {
    if gcd(totient, e) == 1 {
      return e;
    }
    e += 1;
  }
  panic!("This should never happen if totient > 1")
}

/// Generates a random prime number bigger than 1_000_000
pub fn random_prime(first_prime: usize) -> usize {
  let mut n = 1_000_000;
  while !is_prime(n) && n != first_prime {
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
