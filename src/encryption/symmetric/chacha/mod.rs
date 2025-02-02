//! Contains implementation of [`ChaCha`] [`StreamCipher`] algorithm with [`Counter`].
//!
//! Provides implementation of variants:
//! - [`ChaCha20`]: [Original](https://cr.yp.to/chacha/chacha-20080128.pdf) ChaCha variant with 20
//!   rounds
//! - [`ChaCha12`]: [Original](https://cr.yp.to/chacha/chacha-20080128.pdf) ChaCha variant with 12
//!   rounds
//! - [`ChaCha8`]: [Original](https://cr.yp.to/chacha/chacha-20080128.pdf) ChaCha variant with 8
//!   rounds
//! - [`IETFChaCha20`],[`IETFChaCha12`],[`IETFChaCha8`]: [RFC 8439](https://datatracker.ietf.org/doc/html/rfc8439)
//!   with 20, 12, 8 rounds

use crate::encryption::Encryption;

#[cfg(test)] mod tests;

/// length of encryption state
pub const STATE_WORDS: usize = 16;

/// ChaCha encryption algorithm with following constants:
/// - `R`: number of rounds, usually 20, 12, or 8
/// - `N`: nonce's length, IETF version suggests 2 and original ChaCha suggests 1
/// - `C`: big-endian 32-bit counter length, IETF version: 32-byte counter, and original ChaCha:
///   64-byte counter
pub struct ChaCha<const R: usize, const N: usize, const C: usize> {
  key:   [u32; 8],
  nonce: [u32; N],
}

/// IETF [RFC 8439](https://datatracker.ietf.org/doc/html/rfc8439) ChaCha variant with 20 rounds
pub type IETFChaCha20 = ChaCha<20, 3, 1>;
/// IETF [RFC 8439](https://datatracker.ietf.org/doc/html/rfc8439) ChaCha variant with 12 rounds
pub type IETFChaCha12 = ChaCha<12, 3, 1>;
/// IETF [RFC 8439](https://datatracker.ietf.org/doc/html/rfc8439) ChaCha variant with 8 rounds
pub type IETFChaCha8 = ChaCha<8, 3, 1>;

/// [Original](https://cr.yp.to/chacha/chacha-20080128.pdf) ChaCha variant with 20 rounds
pub type ChaCha20 = ChaCha<20, 2, 2>;
/// [Original](https://cr.yp.to/chacha/chacha-20080128.pdf) ChaCha variant with 12 rounds
pub type ChaCha12 = ChaCha<12, 2, 2>;
/// [Original](https://cr.yp.to/chacha/chacha-20080128.pdf) ChaCha variant with 8 rounds
pub type ChaCha8 = ChaCha<8, 2, 2>;

/// Nothing-up-my-sleeve constant used as first four words in encryption state:
/// `["expa", "nd 3", "2-by", "te-k"]`
pub const STATE_CONSTS: [u32; 4] = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574];

/// ChaCha cipher counter consisting of big-endian integer using 32 bits limbs, usually 2 for
/// original variant and 1 for IETF variant
#[derive(Debug, Clone, Copy)]
pub struct Counter<const C: usize> {
  value: [u32; C],
}

impl<const C: usize> Counter<C> {
  /// returns a new Counter
  /// ## Arguments
  /// - `value`: big-endian integer of 32-bit limb
  pub fn new(value: [u32; C]) -> Self { Self { value } }

  /// increases counter value by 1 for each new round of 64-byte input.
  ///
  /// ## Note
  /// Returns `max counter reached` error when counter value reaches maximum allowed by different
  /// counter length. Example: for IETF version, counter length is one, so it throws an error when
  /// counter reaches [`u32::MAX`].
  fn increment(&mut self) -> Result<(), &str> {
    match C {
      0 => Err("counter value is 0"),
      _ => {
        // check for max value
        let mut flag = true;
        for value in self.value.iter() {
          if *value != u32::MAX {
            flag = false;
          }
        }

        if flag {
          return Err("max counter reached");
        }

        let mut add_carry = true;
        for i in (0..C).rev() {
          let (incremented_val, carry) = self.value[i].overflowing_add(add_carry as u32);
          self.value[i] = incremented_val;
          add_carry = carry;
        }

        Ok(())
      },
    }
  }
}

/// computes ChaCha stream cipher block function. It performs following steps:
/// - creates cipher state by concatenating ([`STATE_CONSTS`]|[`Key`]|[`Counter`]|[`Nonce`]) and
///   visualising as 4x4 matrix
/// - scramble the state by performing rounds/2, column rounds and diagonal rounds.
/// - perform (initial state + scrambled state) to add non-linearity
fn block<const N: usize, const C: usize>(
  key: &[u32; 8],
  counter: &Counter<C>,
  nonce: &[u32; N],
  rounds: usize,
) -> [u8; 64] {
  let mut state: Vec<u32> = STATE_CONSTS.to_vec();
  state.extend_from_slice(key);
  state.extend_from_slice(&counter.value);
  state.extend_from_slice(nonce);

  let mut initial_state: [u32; 16] = state
    .clone()
    .try_into()
    .unwrap_or_else(|v: Vec<u32>| panic!("expected vec of len: {} but got: {}", 16, v.len()));

  for _ in 0..rounds / 2 {
    column_rounds(&mut initial_state);
    diagonal_rounds(&mut initial_state);
  }

  let state: [u32; 16] = state
    .into_iter()
    .zip(initial_state)
    .map(|(a, b)| a.wrapping_add(b))
    .collect::<Vec<u32>>()
    .try_into()
    .unwrap_or_else(|v: Vec<u32>| panic!("expected vec of len: {} but got: {}", 16, v.len()));

  let mut output = [0u8; 64];
  state.iter().flat_map(|v| v.to_le_bytes()).enumerate().for_each(|(i, byte)| output[i] = byte);

  output
}

/// quarter round on all 4 columns
const fn column_rounds(state: &mut [u32; STATE_WORDS]) {
  quarter_round(0, 4, 8, 12, state);
  quarter_round(1, 5, 9, 13, state);
  quarter_round(2, 6, 10, 14, state);
  quarter_round(3, 7, 11, 15, state);
}

/// quarter round on 4 diagonals
const fn diagonal_rounds(state: &mut [u32; STATE_WORDS]) {
  quarter_round(0, 5, 10, 15, state);
  quarter_round(1, 6, 11, 12, state);
  quarter_round(2, 7, 8, 13, state);
  quarter_round(3, 4, 9, 14, state);
}

/// ChaCha cipher quarter round that scrambles the state using `Add-Rotate-XOR` operations on four
/// of the state's inputs.
const fn quarter_round(a: usize, b: usize, c: usize, d: usize, state: &mut [u32; STATE_WORDS]) {
  state[a] = state[a].wrapping_add(state[b]);
  state[d] ^= state[a];
  state[d] = state[d].rotate_left(16);

  state[c] = state[c].wrapping_add(state[d]);
  state[b] ^= state[c];
  state[b] = state[b].rotate_left(12);

  state[a] = state[a].wrapping_add(state[b]);
  state[d] ^= state[a];
  state[d] = state[d].rotate_left(8);

  state[c] = state[c].wrapping_add(state[d]);
  state[b] ^= state[c];
  state[b] = state[b].rotate_left(7);
}

impl<const R: usize, const N: usize, const C: usize> ChaCha<R, N, C> {
  /// returns a new ChaCha encryption function
  /// ## Arguments
  /// - [`Key`]: 256-bit key in big-endian 32-bit limbs
  /// - [`Nonce`]: initialisation vector with varying length, 64-bit in original variant and 96-bit
  ///   for [RFC 8439](https://datatracker.ietf.org/doc/html/rfc8439) variant.
  ///
  /// *Note*: same nonce value shouldn't be used with a key as stream ciphers are malleable.
  pub fn new(key: &[u32; 8], nonce: &[u32; N]) -> Self { Self { key: *key, nonce: *nonce } }

  /// Encrypts a plaintext of maximum length $2^{32*C}$ by performing $ENC_k(m) = m ⨁ B(k)$, where
  /// B(k) is pseudoranom keystream calculated using ChaCha block function.
  ///
  /// ## Usage
  /// ```
  /// use rand::{thread_rng, Rng};
  /// use ronkathon::encryption::symmetric::chacha::{ChaCha, Counter};
  /// let mut rng = thread_rng();
  /// let key: [u32; 8] = rng.gen();
  /// let nonce: [u32; 3] = rng.gen();
  ///
  /// let chacha = ChaCha::<20, 3, 1>::new(&key, &nonce);
  ///
  /// let counter: Counter<1> = Counter::new([0]);
  /// // plaintext can be of length `2^{32*i}` 64-byte
  /// let plaintext = b"Hello World!";
  ///
  /// let ciphertext = chacha.encrypt(&counter, plaintext);
  /// ```
  ///
  /// ## Note:
  /// - [`Counter`] can be initialised to any number and is incremented by `1` until it reaches max
  ///   value, i.e. for $C=2$, encryption can happen for $2^64$ 64-byte input.
  /// - counter and nonce length should be equal to 128 bytes
  pub fn encrypt(&self, counter: &Counter<C>, plaintext: &[u8]) -> Result<Vec<u8>, String> {
    // counter and nonce length should be equal to 128 bytes
    if C + N != 4 {
      return Err("invalid counter and nonce lengths".to_string());
    }

    let mut ciphertext: Vec<u8> = Vec::new();

    let mut counter_iter = *counter;

    // parse inputs in chunks of 64 bytes
    let chunks = plaintext.chunks_exact(64);
    let remainder = chunks.remainder();

    for chunk in chunks {
      // compute pseudorandom keystream from key, counter and nonce
      let keystream = block(&self.key, &counter_iter, &self.nonce, R);
      // increment the counter
      counter_iter.increment()?;

      // perform: Enc_k(m) = m ^ B(k)
      let res = keystream.iter().zip(chunk).map(|(a, b)| a ^ b).collect::<Vec<u8>>();

      // serialize encrypted bytes to ciphertext
      ciphertext.extend(res);
    }

    // encrypt remainder plaintext bytes separately
    if !remainder.is_empty() {
      // compute pseudorandom keystream from key, counter and nonce
      let keystream = block(&self.key, &counter_iter, &self.nonce, R);

      // perform: Enc_k(m) = m ^ B(k)
      let res = remainder.iter().zip(keystream).map(|(a, b)| a ^ b).collect::<Vec<u8>>();

      // serialize encrypted bytes to ciphertext
      ciphertext.extend(res);
    }

    Ok(ciphertext)
  }

  /// Decrypts a ciphertext of arbitrary length using [`Self::encrypt`].
  ///
  /// ## Usage
  /// ```
  /// use rand::{thread_rng, Rng};
  /// use ronkathon::encryption::symmetric::chacha::{ChaCha, Counter};
  /// let mut rng = thread_rng();
  /// let key: [u32; 8] = rng.gen();
  /// let nonce: [u32; 3] = rng.gen();
  ///
  /// let chacha = ChaCha::<20, 3, 1>::new(&key, &nonce);
  ///
  /// let counter: Counter<1> = Counter::new([0]);
  /// // plaintext can be of length `2^{32*i}` 64-byte
  /// let plaintext = b"Hello World!";
  ///
  /// let ciphertext = chacha.encrypt(&counter, plaintext).unwrap();
  /// let decrypted = chacha.decrypt(&counter, &ciphertext).unwrap();
  ///
  /// assert_eq!(decrypted, plaintext);
  /// ```
  pub fn decrypt(
    &self,
    counter: &Counter<C>,
    ciphertext: &[u8],
  ) -> Result<Vec<u8>, <Self as Encryption>::Error> {
    self.encrypt(counter, ciphertext)
  }

  /// Encrypts a plaintext of arbitrary length using [`Self::encrypt`] with a given counter.

  fn encrypt_with_counter(
    &self,
    counter: &Counter<C>,
    plaintext: &[u8],
  ) -> Result<Vec<u8>, <Self as Encryption>::Error> {
    self.encrypt(counter, plaintext)
  }

  fn decrypt_with_counter(
    &self,
    counter: &Counter<C>,
    ciphertext: &[u8],
  ) -> Result<Vec<u8>, <Self as Encryption>::Error> {
    self.decrypt(counter, ciphertext)
  }
}

impl<const R: usize, const N: usize, const C: usize> Encryption for ChaCha<R, N, C> {
  type Ciphertext = Vec<u8>;
  type Error = String;
  type Key = [u32; 8];
  type Plaintext = Vec<u8>;

  fn new(key: Self::Key) -> Result<Self, Self::Error> { Ok(Self { key, nonce: [0; N] }) }

  fn encrypt(&self, data: &Self::Plaintext) -> Result<Self::Ciphertext, Self::Error> {
    let counter = Counter::new([0u32; C]);
    self.encrypt(&counter, data)
  }

  fn decrypt(&self, data: &Self::Ciphertext) -> Result<Self::Plaintext, Self::Error> {
    let counter = Counter::new([0u32; C]);
    self.decrypt(&counter, data)
  }
}
