//! Edwards-curve Digital Signature Algorithm (EdDSA) based on the RFC 8032.
use crypto_bigint::{Encoding, U256, U512};
use curve::{Coordinate, ScalarField, ScalarField64, GENERATOR, ORDER};
use sha2::{Digest, Sha512};

pub mod curve;

#[cfg(test)] mod tests;

fn sha512_hash(bytes: &[u8]) -> [u8; 64] {
  let mut hasher = Sha512::new();
  hasher.update(bytes);
  let mut output: [u8; 64] = [0u8; 64];
  output.copy_from_slice(&hasher.finalize());
  output
}

fn clamp(mut bytes: [u8; 32]) -> [u8; 32] {
  for i in 0..3 {
    bytes[0] &= !(1 << i);
  }
  bytes[31] |= 1 << 6;
  bytes[31] &= !(1 << 7);
  bytes
}

fn reduce_by_order(x: [u8; 64]) -> [u8; 32] {
  let r1 = ScalarField64::new(&U512::from_le_bytes(x)).retrieve().to_le_bytes();
  let mut r2 = [0u8; 32];
  r2.copy_from_slice(&r1[..32]);
  r2
}

/// Encapsulates the functions of [`Ed25519`] digital signature scheme.
pub struct Ed25519;

impl Ed25519 {
  /// Generate the `public_key` given the `private_key`.
  /// Both keys are of size 32 bytes.
  /// Returns both the keys as (private_key, public_key) tuple.
  pub fn keygen(private_key: [u8; 32]) -> ([u8; 32], [u8; 32]) {
    let keyhash = sha512_hash(&private_key);
    let mut h = [0u8; 32];
    h.copy_from_slice(&keyhash[..32]);

    let a = ScalarField::new(&U256::from_le_bytes(clamp(h)));
    let public_key = GENERATOR * a;
    (private_key, public_key.encode())
  }

  /// Sign the `msg` using the `public_key` and `private_key`.
  /// Returns the signature of size 64 bytes.
  pub fn sign(private_key: [u8; 32], public_key: [u8; 32], msg: &[u8]) -> [u8; 64] {
    let keyhash = sha512_hash(&private_key);

    let mut a1: [u8; 32] = [0u8; 32];
    a1.copy_from_slice(&keyhash[..32]);
    let a = ScalarField::new(&U256::from_le_bytes(clamp(a1)));

    let mut seed: [u8; 32] = [0u8; 32];
    seed.copy_from_slice(&keyhash[32..]);

    let r1 = [&seed, msg].concat();
    let r2 = sha512_hash(&r1);
    let r3 = reduce_by_order(r2);
    let r = ScalarField::new(&U256::from_le_bytes(r3));

    let big_r = (GENERATOR * r).encode();

    let h1 = [&big_r, &public_key, msg].concat();
    let h2 = sha512_hash(&h1);
    let h = ScalarField::new(&U256::from_le_bytes(reduce_by_order(h2)));

    let s1 = r + h * a;
    let big_s = s1.retrieve().to_le_bytes();

    let mut output = [0u8; 64];
    output[..32].copy_from_slice(&big_r);
    output[32..].copy_from_slice(&big_s);

    output
  }

  /// Verifies message and signature pair given a `public_key`.
  pub fn verify(public_key: [u8; 32], message: &[u8], signature: [u8; 64]) -> bool {
    let mut r = [0u8; 32];
    let mut s = [0u8; 32];
    r.copy_from_slice(&signature[..32]);
    s.copy_from_slice(&signature[32..]);

    let r1 = match Coordinate::decode(r) {
      Some(x) => x,
      None => return false,
    };

    let s_uint = U256::from_le_bytes(s);
    if s_uint >= ORDER {
      return false;
    }

    let s = ScalarField::new(&s_uint);

    let a = match Coordinate::decode(public_key) {
      Some(x) => x,
      None => return false,
    };

    let h1 = [&r, &public_key, message].concat();
    let h2 = sha512_hash(&h1);
    let h = ScalarField::new(&U256::from_le_bytes(reduce_by_order(h2)));

    let mut rhs = r1 + a * h;
    let mut lhs = GENERATOR * s;

    for _ in 0..3 {
      lhs = lhs.double();
      rhs = rhs.double();
    }

    lhs == rhs
  }
}
