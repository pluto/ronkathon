//! Contains cryptographic primitives like symmetric and asymmetric encryption.
pub mod asymmetric;
pub mod symmetric;

/// Core encryption trait that defines basic encryption/decryption operations
pub trait Encryption {
  /// The key type used by this encryption algorithm
  type Key: Clone;
  /// The error type returned by encryption operations
  type Error: std::fmt::Debug;
  /// The data that is input into this scheme for encryption
  type Plaintext;
  /// The encrypted form of the data
  type Ciphertext;
  /// Create a new instance with the given key
  fn new(key: Self::Key) -> Result<Self, Self::Error>
  where Self: Sized;

  /// Encrypt data
  fn encrypt(&self, data: &Self::Plaintext) -> Result<Self::Ciphertext, Self::Error>;

  /// Decrypt data
  fn decrypt(&self, data: &Self::Ciphertext) -> Result<Self::Plaintext, Self::Error>;
}
/// Optional trait for block-specific operations
pub trait BlockOperations: Encryption {
  /// The size of each block in bytes
  const BLOCK_SIZE: usize;
  /// The block type used in block-specific operations
  type Block: AsRef<[u8]> + AsMut<[u8]> + From<Vec<u8>> + Copy + PartialEq;
  /// Encrypt a single block of data
  fn encrypt_block(&self, block: Self::Block) -> Result<Self::Block, Self::Error>;
  /// Decrypt a single block of data
  fn decrypt_block(&self, block: Self::Block) -> Result<Self::Block, Self::Error>;
}
