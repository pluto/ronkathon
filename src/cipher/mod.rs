mod aes;

/// Block size in bits.
pub const BLOCK_LEN: usize = 128;

pub type Block = [u8; BLOCK_LEN];

/// A generic N-bit key.
#[derive(Debug, Copy, Clone)]
pub struct Key<const N: usize>
where [(); N / 8]: {
  inner: [u8; N / 8],
}

impl<const N: usize> Key<N>
where [(); N / 8]:
{
  pub fn new(bytes: [u8; N / 8]) -> Self { Self { inner: bytes } }

  pub fn len() -> usize { N }
}

/// A 128-bit key
pub type Key128 = Key<128>;

/// A 32-bit word
pub type Word = [u8; 4];

/// Typically:
///
/// 10 rounds for 128-bit keys,
/// 12 rounds for 196-bit keys,
/// 14 rounds for 256-bit keys.
pub const NUM_ROUNDS: usize = 10;

/// # How to construct a block cipher:
///
/// 1) A block cipher used in practice is a repetition of rounds:
/// a short sequence of operations that is weak on its own but
/// strong in numbers.
///
/// 2) There are two main techniques:
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
  /// Block size
  const BLOCK_SIZE: usize = B;

  /// Key size in bits.
  const KEY_SIZE: usize = K;

  /// Key size in 32-bit words.
  const KEY_LEN_WORDS: usize = K / 32;

  /// Given a key and a plaintext block, produces a ciphertext block.
  /// This operation can be expressed as C = E(K, P)
  fn encrypt(&mut self, key: Key<K>, plaintext: [u8; 16]) -> Block;

  /// Given a key and a ciphertext block, produces the original plaintext block.
  /// This operation can be expressed as P = D(K, C)
  fn decrypt(self, key: Key<K>, ciphertext: Block) -> Block;
}
