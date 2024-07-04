//! Contains implementation of symmetric encryption primitives.
pub mod aes;
pub mod chacha;
pub mod des;
pub mod modes;

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

/// Trait for stream ciphers
pub trait StreamCipher {
  /// secret key used in encryption and decryption
  type Key;
  /// Initialisation vector (IV)
  type Nonce;
  /// Error originating during encryption
  type Error;
  /// Counter used for some encryption primitives like [`chacha::ChaCha`]
  type Counter;

  /// Create a new Stream cipher object.
  /// ## Arguments
  /// - `key`: secret key used to encrypt/decrypt
  /// - `nonce`: nonce value
  fn new(key: &Self::Key, nonce: &Self::Nonce) -> Result<Self, Self::Error>
  where Self: Sized;

  /// Encrypt a plaintext of arbitrary length bytes
  fn encrypt(&self, plaintext: &[u8]) -> Result<Vec<u8>, Self::Error>;
  /// Decrypt a ciphertext of arbitrary length bytes
  fn decrypt(&self, ciphertext: &[u8]) -> Result<Vec<u8>, Self::Error>;

  /// encrpypt a plaintext with counter that increments with every new block
  fn encrypt_with_counter(
    &self,
    counter: &Self::Counter,
    plaintext: &[u8],
  ) -> Result<Vec<u8>, Self::Error>;

  /// decrypt a ciphertext with counter
  fn decrypt_with_counter(
    &self,
    counter: &Self::Counter,
    ciphertext: &[u8],
  ) -> Result<Vec<u8>, Self::Error>;
}

/// Trait for block ciphers that works on bytes of specific sizes
pub trait BlockCipher {
  /// Block size for cipher operations
  // const BLOCK_SIZE: usize;
  type Block: AsRef<[u8]> + AsMut<[u8]> + From<Vec<u8>> + Copy;
  /// Secret key for encryption/decryption
  type Key;

  /// Creates a new block cipher object
  // fn new(key: &Self::Key) -> Self;

  /// Encrypt a plaintext of arbitrary length and returns ciphertext of same length as plaintext.
  ///
  /// Note: correct padding scheme should be used as per the mode of operation of cipher.
  fn encrypt(key: &Self::Key, plaintext: &Self::Block) -> Self::Block;
  /// Decrypt a ciphertext of arbitrary length and returns plaintext.
  ///
  /// Note: any padded bytes should be removed
  fn decrypt(key: &Self::Key, ciphertext: &Self::Block) -> Self::Block;
}
