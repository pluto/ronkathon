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

use crate::field::FiniteField;

/// A field element for RSA operations with a modulus of P.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Default, PartialOrd)]
pub struct RSAField<const P: usize, const Q: usize> {
  /// The value of the field element
  pub value: usize,
}
/// Constructs a new RSAField element
impl<const P: usize, const Q: usize> RSAField<P, Q> {
  /// Constructs a new RSAField element
  pub const fn new(value: usize) -> Self { Self { value: value % (P * Q) } }

  #[allow(dead_code)]
  /// Encrypts a message using the RSA algorithm
  const fn encrypt(message: u32, e: u32) -> u32 { message.pow(e) % (P * Q) as u32 }

  #[allow(dead_code)]
  /// Decrypts a cipher using the RSA algorithm
  const fn decrypt(cipher: u32, d: u32) -> u32 { cipher.pow(d) % (P * Q) as u32 }

  #[allow(dead_code)]
  /// Generates e value for the RSA algorithm
  const fn generate_e() -> u32 {
    let totient = euler_totient(P as u32, Q as u32);
    let mut e = 2;
    while e < totient {
      if gcd(totient, e) == 1 {
        return e;
      }
      e += 1;
    }
    0 // This should never happen if totient > 1
  }
}

impl<const P: usize, const Q: usize> FiniteField for RSAField<P, Q> {
  const ONE: Self = Self { value: 1 };
  const ORDER: usize = P * Q;
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

impl<const P: usize, const Q: usize> From<usize> for RSAField<P, Q> {
  fn from(val: usize) -> Self { Self::new(val) }
}

impl<const P: usize, const Q: usize> const Add for RSAField<P, Q> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self { Self { value: (self.value + rhs.value) % Self::ORDER } }
}

impl<const P: usize, const Q: usize> AddAssign for RSAField<P, Q> {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<const P: usize, const Q: usize> Sum for RSAField<P, Q> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO)
  }
}

impl<const P: usize, const Q: usize> Sub for RSAField<P, Q> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let (mut diff, over) = self.value.overflowing_sub(rhs.value);
    let corr = if over { Self::ORDER } else { 0 };
    diff = diff.wrapping_add(corr);
    Self { value: diff }
  }
}

impl<const P: usize, const Q: usize> SubAssign for RSAField<P, Q> {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<const P: usize, const Q: usize> Mul for RSAField<P, Q> {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self { Self { value: (self.value * rhs.value) % Self::ORDER } }
}

impl<const P: usize, const Q: usize> MulAssign for RSAField<P, Q> {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<const P: usize, const Q: usize> Product for RSAField<P, Q> {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl<const P: usize, const Q: usize> Div for RSAField<P, Q> {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self { self * rhs.inverse().unwrap() }
}

impl<const P: usize, const Q: usize> DivAssign for RSAField<P, Q> {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl<const P: usize, const Q: usize> Neg for RSAField<P, Q> {
  type Output = Self;

  fn neg(self) -> Self::Output { Self::ZERO - self }
}

impl<const P: usize, const Q: usize> Rem for RSAField<P, Q> {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self { self - (self / rhs) * rhs }
}

const fn euler_totient(prime_1: u32, prime_2: u32) -> u32 { (prime_1 - 1) * (prime_2 - 1) }

const fn gcd(a: u32, b: u32) -> u32 {
  if b == 0 {
    a
  } else {
    gcd(b, a % b)
  }
}

#[allow(dead_code)]
/// Computes the modular inverse of e mod totient
const fn mod_inverse(e: u32, totient: u32) -> u32 {
  let mut d = 1;
  while (d * e) % totient != 1 {
    d += 1;
  }
  d
}

#[cfg(test)]
mod tests {
  use super::*;
  const PRIME_1: usize = 5;
  const PRIME_2: usize = 3;

  #[test]
  fn test_euler_totient() {
    assert_eq!(euler_totient(PRIME_1 as u32, PRIME_2 as u32), 8);
  }

  #[test]
  fn test_gcd() {
    assert_eq!(gcd(10, 5), 5);
    assert_eq!(gcd(10, 3), 1);
  }

  #[test]
  fn test_generate_e() {
    let e = RSAField::<PRIME_1, PRIME_2>::generate_e();
    assert_eq!(e, 3);
  }

  #[test]
  fn test_mod_inverse() {
    assert_eq!(mod_inverse(3, 8), 3);
  }

  #[test]
  fn test_encrypt_decrypt() {
    let message = 10;
    let e = RSAField::<PRIME_1, PRIME_2>::generate_e();
    let d = mod_inverse(e, euler_totient(PRIME_1 as u32, PRIME_2 as u32));
    let cipher = RSAField::<PRIME_1, PRIME_2>::encrypt(message, e);
    let decrypted = RSAField::<PRIME_1, PRIME_2>::decrypt(cipher, d);
    assert_eq!(decrypted, message);
  }
}
