//! This module contains the implementation for the Advanced Encryption Standard (AES) encryption
//! and decryption.
#![cfg_attr(not(doctest), doc = include_str!("./README.md"))]

use itertools::Itertools;

pub mod sbox;
#[cfg(test)] pub mod tests;

use super::BlockCipher;
use crate::encryption::symmetric::aes::sbox::{INVERSE_SBOX, SBOX};

/// A block in AES represents a 128-bit sized message data.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Block(pub [u8; 16]);

impl From<Vec<u8>> for Block {
  fn from(value: Vec<u8>) -> Self {
    assert!(value.len() == 16);
    let val: [u8; 16] = value
      .try_into()
      .unwrap_or_else(|v: Vec<u8>| panic!("expected a vec of len: {} but got: {}", 16, v.len()));
    Self(val)
  }
}

impl AsRef<[u8]> for Block {
  fn as_ref(&self) -> &[u8] { &self.0 }
}

impl AsMut<[u8]> for Block {
  fn as_mut(&mut self) -> &mut [u8] { self.0.as_mut() }
}

///  A word in AES represents a 32-bit array of data.
pub type Word = [u8; 4];

/// A generic N-bit key.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Key<const N: usize>
where [(); N / 8]: {
  inner: [u8; N / 8],
}

impl<const N: usize> Key<N>
where [(); N / 8]:
{
  /// Creates a new `Key` of size `N` bits.
  pub fn new(key_bytes: [u8; N / 8]) -> Self { Self { inner: key_bytes } }
}

impl<const N: usize> std::ops::Deref for Key<N>
where [(); N / 8]:
{
  type Target = [u8; N / 8];

  fn deref(&self) -> &Self::Target { &self.inner }
}
// impl<const N: usize> SymmetricEncryption for AES<N>
// where [(); N / 8]:
// {
//   type Block = Block;
//   type Key = Key<N>;
//
//   /// Encrypt a message of size [`Block`] with a [`Key`] of size `N`-bits.
//   ///
//   /// ## Example
//   /// ```rust
//   /// #![feature(generic_const_exprs)]
//   ///
//   /// use rand::{thread_rng, Rng};
//   /// use ronkathon::encryption::symmetric::{
//   ///   aes::{Key, AES},
//   ///   SymmetricEncryption,
//   /// };
//   ///
//   /// let mut rng = thread_rng();
//   /// let key = Key::<128>::new(rng.gen());
//   /// let plaintext = rng.gen();
//   /// let encrypted = AES::encrypt(&key, &plaintext);
//   /// ```
//   fn encrypt(key: &Self::Key, plaintext: &Self::Block) -> Self::Block {
//     let num_rounds = match N {
//       128 => 10,
//       192 => 12,
//       256 => 14,
//       _ => panic!("AES only supports key sizes 128, 192 and 256 bits. You provided: {N}"),
//     };
//
//     Self::aes_encrypt(plaintext, key, num_rounds)
//   }
//
//   fn decrypt(_key: &Self::Key, _ciphertext: &Self::Block) -> Self::Block { unimplemented!() }
// }

/// Contains the values given by [x^(i-1), {00}, {00}, {00}], with x^(i-1)
/// being powers of x in the field GF(2^8).
///
/// NOTE: i starts at 1, not 0.
const ROUND_CONSTANTS: [[u8; 4]; 10] = [
  [0x01, 0x00, 0x00, 0x00],
  [0x02, 0x00, 0x00, 0x00],
  [0x04, 0x00, 0x00, 0x00],
  [0x08, 0x00, 0x00, 0x00],
  [0x10, 0x00, 0x00, 0x00],
  [0x20, 0x00, 0x00, 0x00],
  [0x40, 0x00, 0x00, 0x00],
  [0x80, 0x00, 0x00, 0x00],
  [0x1B, 0x00, 0x00, 0x00],
  [0x36, 0x00, 0x00, 0x00],
];

/// A struct containing an instance of an AES encryption/decryption.
#[derive(Clone)]
pub struct AES<const N: usize> {}

/// Instead of arranging its bytes in a line (array),
/// AES operates on a grid, specifically a 4x4 column-major array:
///
/// [[b_0, b_4, b_8,  b_12],
///  [b_1, b_5, b_9,  b_13],
///  [b_2, b_6, b_10, b_14],
///  [b_3, b_7, b_11, b_15]]
///
/// where b_i is the i-th byte. This is also how we will layout
/// bytes in our `State`.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
struct State([[u8; 4]; 4]);

/// Multiplies a 8-bit number in the Galois field GF(2^8). This is done using "carry-less
/// multiplication" or "bitwise multiplication", where the binary representation of each
/// element is treated as a polynomial.
///
/// NOTE: this multiplication is not commutative - ie. A * B may not equal B * A.
fn galois_multiplication(mut col: u8, mut multiplicant: usize) -> u8 {
  let mut product = 0;

  for _ in 0..8 {
    if multiplicant & 1 == 1 {
      product ^= col;
    }

    let hi_bit = col & 0x80;
    col <<= 1;
    if hi_bit == 0x80 {
      col ^= 0x1B; // This XOR brings the value back into the field if an overflow occurs
                   // (ie. hi_bit is set)
    }

    multiplicant >>= 1;
  }
  product
}

impl<const N: usize> AES<N>
where [(); N / 8]:
{
  /// Performs the cipher, with key size of `N` (in bits), as seen in Figure 5 of the document
  /// linked in the front-page.
  fn aes_encrypt(plaintext: &[u8; 16], key: &Key<N>, num_rounds: usize) -> Block {
    assert!(!key.is_empty(), "Key is not instantiated");

    let key_len_words = N / 32;
    let mut round_keys_words = Vec::with_capacity(key_len_words * (num_rounds + 1));
    Self::key_expansion(*key, &mut round_keys_words, key_len_words, num_rounds);
    let mut round_keys = round_keys_words.chunks_exact(4);

    let mut state = State(
      plaintext
        .chunks(4)
        .map(|c| c.try_into().unwrap())
        .collect::<Vec<[u8; 4]>>()
        .try_into()
        .unwrap(),
    );
    assert!(state != State::default(), "State is not instantiated");

    // Round 0 - add round key
    Self::add_round_key(&mut state, round_keys.next().unwrap());

    // Rounds 1 to N - 1
    for _ in 1..num_rounds {
      Self::sub_bytes(&mut state);
      Self::shift_rows(&mut state);
      Self::mix_columns(&mut state);
      Self::add_round_key(&mut state, round_keys.next().unwrap());
    }

    // Last round - we do not mix columns here.
    Self::sub_bytes(&mut state);
    Self::shift_rows(&mut state);
    Self::add_round_key(&mut state, round_keys.next().unwrap());

    assert!(
      round_keys.remainder().is_empty(),
      "Round keys not fully consumed - perhaps check key expansion?"
    );

    Block(state.0.into_iter().flatten().collect::<Vec<_>>().try_into().unwrap())
  }

  /// Deciphers a given `ciphertext`, with key size of `N` (in bits), as seen in Figure 5 of the
  /// document linked in the front-page.
  fn aes_decrypt(ciphertext: &[u8; 16], key: &Key<N>, num_rounds: usize) -> Block {
    assert!(!key.is_empty(), "Key is not instantiated");

    let key_len_words = N / 32;
    let mut round_keys_words = Vec::with_capacity(key_len_words * (num_rounds + 1));
    Self::key_expansion(*key, &mut round_keys_words, key_len_words, num_rounds);
    // For decryption; we use the round keys from the back, so we iterate from the back here.
    let mut round_keys = round_keys_words.chunks_exact(4).rev();

    let mut state = State(
      ciphertext
        .chunks(4)
        .map(|c| c.try_into().unwrap())
        .collect::<Vec<[u8; 4]>>()
        .try_into()
        .unwrap(),
    );
    assert!(state != State::default(), "State is not instantiated");

    // Round 0 - add round key
    Self::add_round_key(&mut state, round_keys.next().unwrap());

    // Rounds 1 to N - 1
    for _ in 1..num_rounds {
      Self::inv_shift_rows(&mut state);
      Self::inv_sub_bytes(&mut state);
      Self::add_round_key(&mut state, round_keys.next().unwrap());
      Self::inv_mix_columns(&mut state);
    }

    // Last round - we do not mix columns here.
    Self::inv_shift_rows(&mut state);
    Self::inv_sub_bytes(&mut state);
    Self::add_round_key(&mut state, round_keys.next().unwrap());

    assert!(
      round_keys.next().is_none(),
      "Round keys not fully consumed - perhaps check key expansion?"
    );

    state.0.into_iter().flatten().collect::<Vec<_>>().try_into().unwrap()
  }

  /// XOR a round key to its internal state.
  fn add_round_key(state: &mut State, round_key: &[[u8; 4]]) {
    for (col, word) in state.0.iter_mut().zip(round_key.iter()) {
      for (c, w) in col.iter_mut().zip(word.iter()) {
        *c ^= w;
      }
    }
  }

  /// Substitutes each byte [s_0, s_1, ..., s_15] with another byte according to a substitution box
  /// (usually referred to as an S-box).
  fn sub_bytes(state: &mut State) {
    for i in 0..4 {
      for j in 0..4 {
        state.0[i][j] = SBOX[state.0[i][j] as usize];
      }
    }
  }

  /// Substitutes each byte [s_0, s_1, ..., s_15] with another byte according to a substitution box
  /// (usually referred to as an S-box).
  ///
  /// Note that the only difference here from [`Self::sub_bytes`] is that we use a different
  /// substitution box [`INVERSE_SBOX`], which is derived differently.
  fn inv_sub_bytes(state: &mut State) {
    for i in 0..4 {
      for j in 0..4 {
        state.0[i][j] = INVERSE_SBOX[state.0[i][j] as usize];
      }
    }
  }

  /// Shift i-th row of i positions, for i ranging from 0 to 3.
  ///
  /// For row 0, no shifting occurs, for row 1, a **left** shift of 1 index occurs, ..
  ///
  /// Note that since our state is in column-major form, we transpose the state to a
  /// row-major form to make this step simpler.
  fn shift_rows(state: &mut State) {
    let len = state.0.len();
    let mut iters: Vec<_> = state.0.into_iter().map(|n| n.into_iter()).collect();

    // Transpose to row-major form
    let mut transposed: Vec<_> =
      (0..len).map(|_| iters.iter_mut().map(|n| n.next().unwrap()).collect::<Vec<_>>()).collect();

    for (r, i) in transposed.iter_mut().zip(0..4) {
      r.rotate_left(i);
    }
    let mut iters: Vec<_> = transposed.into_iter().map(|n| n.into_iter()).collect();

    state.0 = (0..len)
      .map(|_| iters.iter_mut().map(|n| n.next().unwrap()).collect::<Vec<_>>().try_into().unwrap())
      .collect::<Vec<_>>()
      .try_into()
      .unwrap();
  }

  /// The inverse of [`Self::shift_rows`].
  ///
  /// Shift i-th row of i positions, for i ranging from 0 to 3.
  ///
  /// For row 0, no shifting occurs, for row 1, a **right** shift of 1 index occurs, ..
  ///
  /// Note that since our state is in column-major form, we transpose the state to a
  /// row-major form to make this step simpler.
  fn inv_shift_rows(state: &mut State) {
    let len = state.0.len();
    let mut iters: Vec<_> = state.0.into_iter().map(|n| n.into_iter()).collect();

    // Transpose to row-major form
    let mut transposed: Vec<_> =
      (0..len).map(|_| iters.iter_mut().map(|n| n.next().unwrap()).collect::<Vec<_>>()).collect();

    for (r, i) in transposed.iter_mut().zip(0..4) {
      r.rotate_right(i);
    }
    let mut iters: Vec<_> = transposed.into_iter().map(|n| n.into_iter()).collect();

    state.0 = (0..len)
      .map(|_| iters.iter_mut().map(|n| n.next().unwrap()).collect::<Vec<_>>().try_into().unwrap())
      .collect::<Vec<_>>()
      .try_into()
      .unwrap();
  }

  /// Applies the same linear transformation to each of the four columns of the state.
  ///
  /// Mix columns is done as such:
  ///
  /// Each column of bytes is treated as a 4-term polynomial, multiplied modulo x^4 + 1 with a fixed
  /// polynomial a(x) = 3x^3 + x^2 + x + 2. This is done using matrix multiplication.
  fn mix_columns(state: &mut State) {
    for col in state.0.iter_mut() {
      let tmp = *col;

      // 2a0 + 3a1 + a2 + a3
      col[0] =
        galois_multiplication(tmp[0], 2) ^ tmp[3] ^ tmp[2] ^ galois_multiplication(tmp[1], 3);
      // a0 + 2a1 + 3a2 + a3
      col[1] =
        galois_multiplication(tmp[1], 2) ^ tmp[0] ^ tmp[3] ^ galois_multiplication(tmp[2], 3);
      // a0 + a1 + 2a2 + 3a3
      col[2] =
        galois_multiplication(tmp[2], 2) ^ tmp[1] ^ tmp[0] ^ galois_multiplication(tmp[3], 3);
      // 3a0 + a1 + a2 + 2a3
      col[3] =
        galois_multiplication(tmp[3], 2) ^ tmp[2] ^ tmp[1] ^ galois_multiplication(tmp[0], 3);
    }
  }

  /// The inverse of [`Self::mix_columns`].
  ///
  /// Applies the same linear transformation to each of the four columns of the state.
  ///
  /// Mix columns is done as such:
  ///
  /// Each column of bytes is treated as a 4-term polynomial, multiplied modulo x^4 + 1 with a
  /// fixed polynomial a^-1(x) = 11x^3 + 13x^2 + 9x + 14, which is the inverse of the polynomial
  /// used in [`Self::mix_columns`]. This is done using matrix multiplication.
  fn inv_mix_columns(state: &mut State) {
    for col in state.0.iter_mut() {
      let tmp = *col;

      // 14a0 + 11a1 + 13a2 + 9a3
      col[0] = galois_multiplication(tmp[0], 14)
        ^ galois_multiplication(tmp[3], 9)
        ^ galois_multiplication(tmp[2], 13)
        ^ galois_multiplication(tmp[1], 11);
      // 9a0 + 14a1 + 11a2 + 13a3
      col[1] = galois_multiplication(tmp[1], 14)
        ^ galois_multiplication(tmp[0], 9)
        ^ galois_multiplication(tmp[3], 13)
        ^ galois_multiplication(tmp[2], 11);
      // 13a0 + 9a1 + 14a2 + 11a3
      col[2] = galois_multiplication(tmp[2], 14)
        ^ galois_multiplication(tmp[1], 9)
        ^ galois_multiplication(tmp[0], 13)
        ^ galois_multiplication(tmp[3], 11);
      // 11a0 + 13a1 + 9a2 + 14a3
      col[3] = galois_multiplication(tmp[3], 14)
        ^ galois_multiplication(tmp[2], 9)
        ^ galois_multiplication(tmp[1], 13)
        ^ galois_multiplication(tmp[0], 11);
    }
  }

  /// In AES, rotword() is just a one-byte left circular shift.
  fn rotate_word(word: &mut [u8; 4]) { word.rotate_left(1) }

  /// In AES, subword() is just an application of the S-box to each of the
  /// four bytes of a word.
  fn sub_word(mut word: [u8; 4]) -> [u8; 4] {
    word.iter_mut().for_each(|b| *b = SBOX[*b as usize]);

    word
  }

  /// Generates a key schedule based on a given cipher key `Key`, generating a total of
  /// `Nb * (Nr + 1)` words, where Nb = size of block (in words), and Nr = number of rounds.
  /// Nr is determined by the size `N` of the key. Every 4-word chunk from this output
  /// is used as a round key.
  ///
  /// Key expansion ensures that each key used per round is different, introducing additional
  /// complexity and diffusion.
  fn key_expansion(
    key: Key<N>,
    round_keys_words: &mut Vec<Word>,
    key_len: usize,
    num_rounds: usize,
  ) {
    let block_num_words = 128 / 32;

    let out_len = block_num_words * (num_rounds + 1);
    let key_words: Vec<Word> = key.chunks(4).map(|c| c.try_into().unwrap()).collect();
    round_keys_words.extend(key_words);

    for i in key_len..(block_num_words * (num_rounds + 1)) {
      let mut last = *round_keys_words.last().unwrap();

      if i % key_len == 0 {
        Self::rotate_word(&mut last);
        last = (u32::from_le_bytes(Self::sub_word(last))
          ^ u32::from_le_bytes(ROUND_CONSTANTS[(i / key_len) - 1]))
        .to_le_bytes();
      } else if key_len > 6 && i % key_len == 4 {
        last = Self::sub_word(last)
      }

      let round_key = round_keys_words[i - key_len]
        .iter()
        .zip(last.iter())
        .map(|(w, l)| w ^ l)
        .collect_vec()
        .try_into()
        .unwrap();
      round_keys_words.push(round_key);
    }

    assert_eq!(
      round_keys_words.len(),
      out_len,
      "Wrong number of words output during key expansion"
    );
  }
}

impl<const N: usize> BlockCipher for AES<N>
where [(); N / 8]:
{
  // const BLOCK_SIZE: usize = 16;
  type Block = Block;
  type Key = Key<N>;

  /// Encrypt a message of size [`Block`] with a [`Key`] of size `N`-bits.
  ///
  /// ## Example
  /// ```rust
  /// #![feature(generic_const_exprs)]
  ///
  /// use rand::{thread_rng, Rng};
  /// use ronkathon::encryption::symmetric::{
  ///   aes::{Key, AES},
  ///   SymmetricEncryption,
  /// };
  ///
  /// let mut rng = thread_rng();
  /// let key = Key::<128>::new(rng.gen());
  /// let plaintext = rng.gen();
  /// let encrypted = AES::encrypt(&key, &plaintext);
  /// ```
  fn encrypt(key: &Self::Key, plaintext: &Self::Block) -> Self::Block {
    let num_rounds = match N {
      128 => 10,
      192 => 12,
      256 => 14,
      _ => panic!("AES only supports key sizes 128, 192 and 256 bits. You provided: {N}"),
    };

    Self::aes_encrypt(&plaintext.0, key, num_rounds)
  }

  fn decrypt(_key: &Self::Key, _ciphertext: &Self::Block) -> Self::Block { unimplemented!() }
}
