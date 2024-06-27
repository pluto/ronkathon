//! This module contains the implementation of common ciphers.

pub mod aes;

/// Block size in bits.
pub struct Block<const LEN: usize>([u8; LEN]);

/// A generic N-bit key.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Key<const N: usize>
where [(); N / 8]: {
  inner: [u8; N / 8],
}

impl<const N: usize> std::ops::Deref for Key<N>
where [(); N / 8]:
{
  type Target = [u8; N / 8];

  fn deref(&self) -> &Self::Target { &self.inner }
}

impl<const N: usize> Key<N>
where [(); N / 8]:
{
  /// Creates a new `Key` of `N` bits.
  pub fn new(bytes: [u8; N / 8]) -> Self { Self { inner: bytes } }
}

/// A 32-bit word
pub type Word = [u8; 4];

/// # How to construct a block cipher
///
/// A block cipher used in practice is a repetition of rounds:
/// a short sequence of operations that is weak on its own but
/// strong in numbers.
///
/// There are two main techniques:
/// substitution-permutation networks (AES),
/// and Feistal schemes (DES).
///
/// # Security
///
/// Its security is determined by its block size and its key size.
///
/// Blocks shouldn't be too large to to minimize the length of ciphertext
/// and memory footprint, but it also shouldn't be too small; otherwise,
/// they might be susceptible to codebook attacks.
pub trait BlockCipher<const B: usize, const K: usize>
where [(); K / 8]: {
  /// Block size in bits.
  const BLOCK_SIZE: usize = B;

  /// Key size in bits.
  const KEY_SIZE: usize = K;

  /// Key size in bytes.
  const KEY_LEN_BYTES: usize = K / 8;

  /// Key size in 32-bit words.
  const KEY_LEN_WORDS: usize = K / 32;

  /// Produce a ciphertext block given a key and a plaintext block.
  /// This operation can be expressed as C = E(K, P)
  fn encrypt(&mut self, key: Key<K>, plaintext: [u8; 16]) -> Block<B>;

  /// Produce the original plaintext block given a key and a ciphertext block.
  /// This operation can be expressed as P = D(K, C)
  fn decrypt(self, key: Key<K>, ciphertext: Block<B>) -> Block<B>;
}
