//! Contains auxiliary cryptographic functions for Kyber KEM.
//! - [`prf`] - Pseudorandom function
//! - [`h`], [`g`] - Hash function
//! - [`Xof`] - Extendable output function

use crate::hashes::sha3::{Sha3_256, Sha3_512, Shake128, Shake256};

pub fn prf<const ETA: usize>(s: &[u8], b: u8) -> [u8; 64 * ETA] {
  assert!(s.len() == 32);

  let mut hasher = Shake256::new();
  hasher.update(s);
  hasher.update(&[b]);
  let mut res = [0u8; 64 * ETA];
  hasher.squeeze(&mut res);
  res
}

pub fn h(s: &[u8]) -> [u8; 32] {
  let mut hasher = Sha3_256::new();
  hasher.update(s);
  hasher.finalize()
}

pub fn j(s: &[u8]) -> [u8; 32] {
  let mut hasher = Shake256::new();
  hasher.update(s);
  let mut res = [0u8; 32];
  hasher.squeeze(&mut res);
  res
}

pub fn g(c: &[u8]) -> ([u8; 32], [u8; 32]) {
  let mut hasher = Sha3_512::new();
  hasher.update(c);
  let res = hasher.finalize();
  let (h0, h1) = res.split_at(32);
  (h0.try_into().unwrap(), h1.try_into().unwrap())
}

pub struct Xof(Shake128);

impl Xof {
  pub fn init() -> Self { Self(Shake128::new()) }

  pub fn absorb(&mut self, input: &[u8]) { self.0.update(input); }

  pub fn squeeze(&mut self, output: &mut [u8]) { self.0.squeeze(output); }
}
