//! Contains implementation of symmetric encryption primitives.
pub mod des;

/// Trait for symmetric encryption primitive
pub trait SymmetricEncryption {
  /// Key represents the secret key or subkeys used during the encryption algorithm
  type Key;
  /// Block represents message type on which encryption is performed
  type Block;

  /// Encrypts plaintext using key and returns ciphertext
  fn encrypt(key: &Self::Key, plaintext: &Self::Block) -> Self::Block;

  /// Decrypts ciphertext using key and returns plaintext
  fn decrypt(key: &Self::Key, ciphertext: &Self::Block) -> Self::Block;
}
