use rand::{rngs::OsRng, Rng};

use crate::hashes::sha3::{Sha3, Shake128};

/// Size of hash output in bytes (256 bits)
const HASH_SIZE: usize = 32;
/// Number of pairs in the private/public key (one pair per output bit)
const NUM_PAIRS: usize = HASH_SIZE * 8;

/// Lamport private key
///
/// Contains two random values for each bit position in the message digest.
#[derive(Clone)]
pub struct PrivateKey {
  /// 2 random values for each bit position
  key_pairs: [[u8; HASH_SIZE]; NUM_PAIRS * 2],
}

/// Lamport public key
///
/// Contains hash values of each element in the private key.
#[derive(Clone)]
pub struct PublicKey {
  /// Hash of each private key element
  hashed_pairs: [[u8; HASH_SIZE]; NUM_PAIRS * 2],
}

/// Lamport signature
///
/// Contains one value from each pair in the private key, selected
/// based on the corresponding bit in the message digest.
pub struct Signature {
  /// Selected private key elements
  revealed_keys: [[u8; HASH_SIZE]; NUM_PAIRS],
}

impl PrivateKey {
  /// Generate a new random private key
  pub fn generate() -> Self {
    let mut rng = OsRng;
    let mut key_pairs = [[0u8; HASH_SIZE]; NUM_PAIRS * 2];

    // Generate 2 random values for each bit position
    for pair in key_pairs.iter_mut() {
      rng.fill(pair);
    }

    Self { key_pairs }
  }

  /// Sign a message using this private key
  ///
  /// # Arguments
  ///
  /// * `message` - The message to sign
  ///
  /// # Returns
  ///
  /// A Lamport signature for the given message
  ///
  /// # Warning
  ///
  /// This key should only be used once. Reusing it compromises security.
  pub fn sign(&self, message: &[u8]) -> Signature {
    // Hash the message
    let message_digest = hash_message(message);
    let mut revealed_keys = [[0u8; HASH_SIZE]; NUM_PAIRS];

    // For each bit in the message digest, select corresponding private key
    for (i, revealed) in revealed_keys.iter_mut().enumerate() {
      let bit_idx = i / 8;
      let bit_pos = i % 8;
      let bit = (message_digest[bit_idx] >> bit_pos) & 1;

      // Select private key element based on bit value (0 or 1)
      let selected_idx = i * 2 + bit as usize;
      revealed.copy_from_slice(&self.key_pairs[selected_idx]);
    }

    Signature { revealed_keys }
  }

  /// Generate the corresponding public key
  pub fn public_key(&self) -> PublicKey {
    let mut hashed_pairs = [[0u8; HASH_SIZE]; NUM_PAIRS * 2];

    // Hash each element of the private key
    for (i, pair) in self.key_pairs.iter().enumerate() {
      hashed_pairs[i] = hash_message(pair);
    }

    PublicKey { hashed_pairs }
  }
}

impl PublicKey {
  /// Verify a signature against a message
  ///
  /// # Arguments
  ///
  /// * `message` - The message to verify
  /// * `signature` - The signature to verify
  ///
  /// # Returns
  ///
  /// `true` if the signature is valid, `false` otherwise
  pub fn verify(&self, message: &[u8], signature: &Signature) -> bool {
    // Hash the message
    let message_digest = hash_message(message);

    // For each bit in the message digest, verify corresponding signature element
    for (i, revealed) in signature.revealed_keys.iter().enumerate() {
      let bit_idx = i / 8;
      let bit_pos = i % 8;
      let bit = (message_digest[bit_idx] >> bit_pos) & 1;

      // Compute index in public key based on bit value
      let pub_key_idx = i * 2 + bit as usize;

      // Hash the revealed private key and compare with public key
      let hashed_revealed = hash_message(revealed);
      if hashed_revealed != self.hashed_pairs[pub_key_idx] {
        return false;
      }
    }

    true
  }
}

/// Generate a keypair (private key and corresponding public key)
pub fn generate_keypair() -> (PrivateKey, PublicKey) {
  let private_key = PrivateKey::generate();
  let public_key = private_key.public_key();
  (private_key, public_key)
}

/// Hash a message to produce a digest
fn hash_message(message: &[u8]) -> [u8; HASH_SIZE] {
  let mut hasher = Sha3::<HASH_SIZE>::new();
  hasher.update(message);
  let digest = hasher.finalize();

  let mut result = [0u8; HASH_SIZE];
  result.copy_from_slice(&digest[..HASH_SIZE]);
  result
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_sign_verify() {
    let message = b"This is a test message";
    let (private_key, public_key) = generate_keypair();

    // Sign the message
    let signature = private_key.sign(message);

    // Verify the signature
    assert!(public_key.verify(message, &signature));
  }

  #[test]
  fn test_invalid_message() {
    let message = b"This is a test message";
    let altered_message = b"This is a different message";
    let (private_key, public_key) = generate_keypair();

    // Sign the original message
    let signature = private_key.sign(message);

    // Verify with an altered message should fail
    assert!(!public_key.verify(altered_message, &signature));
  }

  #[test]
  fn test_invalid_signature() {
    let message = b"This is a test message";
    let (private_key, public_key) = generate_keypair();

    // Create a signature
    let mut signature = private_key.sign(message);

    // Alter the signature
    signature.revealed_keys[0][0] ^= 0xFF;

    // Verification should fail
    assert!(!public_key.verify(message, &signature));
  }
}
