//! Contains implementation of asymmetric cryptographic primitives like RSA encryption.
pub mod lwe;
pub mod rsa;

pub trait AsymmetricEncryption {
  type PublicKey;
  type PrivateKey;
  type Plaintext;
  type Ciphertext;

  /// Encrypts plaintext using key and returns ciphertext
  fn encrypt(&self, plaintext: &Self::Plaintext) -> Self::Ciphertext;

  /// Decrypts ciphertext using key and returns plaintext
  fn decrypt(&self, ciphertext: &Self::Ciphertext) -> Self::Plaintext;
}
