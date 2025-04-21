//! Edwards-curve Digital Signature Algorithm (EdDSA) based on the RFC 8032.
//!
//! References:
//!     1. [RFC8032] "Edwards-Curve Digital Signature Algorithm (EdDSA)".
use crypto_bigint::{Encoding, U256, U512};
use curve::{Coordinate, ScalarField, ScalarField64, GENERATOR, ORDER};
use rand::Rng;

use crate::hashes::sha::Sha512;

pub mod curve;

#[cfg(test)] mod tests;

fn clamp(mut bytes: [u8; 32]) -> [u8; 32] {
  // Set the first three bits to zero.
  for i in 0..3 {
    bytes[0] &= !(1 << i);
  }
  // Set the last second bit to one.
  bytes[31] |= 1 << 6;
  // Set the last bit to zero.
  bytes[31] &= !(1 << 7);
  bytes
}

/// Calculates `x (mod L)`, where L(see `curve.rs`) is the order of the curve subgroup.
/// Returns it result as a 32-byte array.
fn reduce_by_order(x: [u8; 64]) -> [u8; 32] {
  // ScalarField64 calculates the modulus of 64-byte/512-bit number with `L`(the order of the
  // subgroup)
  let r1 = ScalarField64::new(&U512::from_le_bytes(x)).retrieve().to_le_bytes();
  let mut r2 = [0u8; 32];
  r2.copy_from_slice(&r1[..32]);
  r2
}

/// Encapsulates the functions of [`Ed25519`] digital signature scheme.
pub struct Ed25519 {
  secret_key: [u8; 32],
  public_key: [u8; 32],
}

impl Ed25519 {
  /// Generates the `public_key` using the `secret_key`, if given, otherwise randomly generates
  /// one.
  ///
  /// Returns an instance of Ed25519 struct with secret_key and public_key within it.
  pub fn new(secret_key: Option<[u8; 32]>) -> Self {
    let sk = match secret_key {
      Some(sk) => sk,
      None => {
        let mut rng = rand::thread_rng();
        let v: Vec<_> = (0..32).map(|_| rng.gen_range(0..=255)).collect();
        let mut a = [0u8; 32];
        a.copy_from_slice(&v);
        a
      },
    };

    let hashfunc = Sha512::new();
    let keyhash = hashfunc.digest(&sk);
    let mut h = [0u8; 32];
    h.copy_from_slice(&keyhash[..32]);

    let a = ScalarField::new(&U256::from_le_bytes(clamp(h)));
    let public_key = GENERATOR * a;
    Self { secret_key: sk, public_key: public_key.encode() }
  }

  /// Sign the `message` using the `public_key` and `secret_key`.
  ///
  /// It uses the algorithm given in Section 5.1.6 of [RFC8032], which is as follows:
  ///       Notation: `H` <- SHA-512 hash function,
  ///                 `Enc` <- Encoding function for a point on curve. See `curve.rs`
  ///
  /// 1. `h = H(secret_key)`, 64-byte hash of secret_key
  /// 2. Split `h` into two 32-byte halves, `s` and `prefix`. `s` is converted to an element of the
  ///    scalar field.
  /// 3. `r = H(prefix | message)`, hash of prefix concatenated with the message. `r` is converted
  ///    to an element of the scalar field.
  /// 4. `R = Enc(r * B)`, the encoding of scalar multiplication of `B`, the generator the curve
  ///    group, with `r`, the scalar from the previous step.
  /// 5. `k = H(R | public_key | message)`, k is converted to an element of the scalar field.
  /// 6. `S = r + k * s`, where addition and multiplication are of the scalar field.
  ///
  /// The 32-byte R and S are concatenated to form the 64-byte signature.
  pub fn sign(&self, message: &[u8]) -> [u8; 64] {
    let hashfunc = Sha512::new();
    let keyhash = hashfunc.digest(&self.secret_key);

    let mut s1: [u8; 32] = [0u8; 32];
    s1.copy_from_slice(&keyhash[..32]);
    let s = ScalarField::new(&U256::from_le_bytes(clamp(s1)));

    let mut prefix: [u8; 32] = [0u8; 32];
    prefix.copy_from_slice(&keyhash[32..]);

    let r1 = [&prefix, message].concat();
    let r2 = hashfunc.digest(&r1);
    let r3 = reduce_by_order(r2.try_into().unwrap());
    let r = ScalarField::new(&U256::from_le_bytes(r3));

    let big_r = (GENERATOR * r).encode();

    let k1 = [&big_r, &self.public_key, message].concat();
    let k2 = hashfunc.digest(&k1);
    let k = ScalarField::new(&U256::from_le_bytes(reduce_by_order(k2.try_into().unwrap())));

    let s1 = r + k * s;
    let big_s = s1.retrieve().to_le_bytes();

    let mut output = [0u8; 64];
    output[..32].copy_from_slice(&big_r);
    output[32..].copy_from_slice(&big_s);

    output
  }

  /// Verify the `signature` on a `message` using the `public_key`
  ///
  /// It uses the algorithm given in Section 5.1.7 of [RFC8032], which is as follows:
  ///       Notation: H <- SHA-512 hash function,
  ///                 Decode <- Decoding function for a point on curve. See `curve.rs`
  ///
  /// 1. Split the signature into two 32-byte halves, R and S. R is decoded into a point on the
  ///    curve. S is converted to an element of the scalar field.
  /// 2. `A = Decode(public_key)`, decode the public_key to a point on the curve.
  /// 3. `k = H(R | public_key | message)`, hash of first 32-byte of signature concatenated with
  ///    public_key and the message. `k` is then converted to an element of the scalar field.
  /// 4. Check if `8 * S * B` == `8*(R + k*A)`.
  pub fn verify(&self, message: &[u8], signature: [u8; 64]) -> bool {
    let mut big_r = [0u8; 32];
    let mut big_s = [0u8; 32];
    big_r.copy_from_slice(&signature[..32]);
    big_s.copy_from_slice(&signature[32..]);

    // Decode `big_r` into a point
    let r = match Coordinate::decode(big_r) {
      Some(x) => x,
      None => return false,
    };

    // Represent `big_s` into a `ScalarField` element.
    let s_uint = U256::from_le_bytes(big_s);
    if s_uint >= ORDER {
      return false;
    }
    let s = ScalarField::new(&s_uint);

    // Decode the public_key as a point.
    let a = match Coordinate::decode(self.public_key) {
      Some(x) => x,
      None => return false,
    };

    let k1 = [&big_r, &self.public_key, message].concat();
    let hashfunc = Sha512::new();
    let k2 = hashfunc.digest(&k1);
    let k = ScalarField::new(&U256::from_le_bytes(reduce_by_order(k2.try_into().unwrap())));

    let mut rhs = r + a * k;
    let mut lhs = GENERATOR * s;

    // Calculates 8*lhs and 8*rhs
    for _ in 0..3 {
      lhs = lhs.double();
      rhs = rhs.double();
    }

    lhs == rhs
  }
}
