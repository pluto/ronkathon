//! Contains implementation for Counter (CTR) mode of operation in block ciphers

use crate::encryption::symmetric::{counter::Counter, BlockCipher};

/// [`BlockCipher`] counter mode of operation
pub struct CTR<C: BlockCipher>
where [(); C::BLOCK_SIZE / 2]: {
  nonce: [u8; C::BLOCK_SIZE / 2],
}

impl<C: BlockCipher> CTR<C>
where [(); C::BLOCK_SIZE / 2]:
{
  /// Create a CTR mode of operation object
  /// # Arguments
  /// - `nonce`: *Non-repeating* IV of [`BlockCipher::BLOCK_SIZE`]/2 bytes. Nonce is concatenated
  ///   with [`Counter`] to generate a keystream that does not repeat for a long time.
  pub fn new(nonce: [u8; C::BLOCK_SIZE / 2]) -> Self { Self { nonce } }

  /// Encrypt a plaintext with [`BlockCipher::Key`] and [`Counter`]
  /// ## Arguments
  /// - `key`: secret key used for [`BlockCipher`]
  /// - `counter`: Increment-by-one counter concatenated with nonce as IV for each block.
  /// - `plaintext`: data to be encrypted
  /// ## Usage
  /// ```
  /// #![allow(incomplete_features)]
  /// #![feature(generic_const_exprs)]
  /// use rand::{thread_rng, Rng};
  /// use ronkathon::encryption::symmetric::{
  ///   aes::{Key, AES},
  ///   counter::Counter,
  ///   modes::ctr::CTR,
  ///   BlockCipher,
  /// };
  ///
  /// let mut rng = thread_rng();
  /// let rand_key: [u8; 16] = rng.gen();
  /// let key = Key::<128>::new(rand_key);
  /// let nonce: [u8; AES::<128>::BLOCK_SIZE / 2] = rng.gen();
  /// let counter: Counter<{ AES::<128>::BLOCK_SIZE / 2 }> = Counter::from(0);
  ///
  /// let ctr = CTR::<AES<128>>::new(nonce);
  /// let plaintext = b"Hello World!";
  ///
  /// let ciphertext = ctr.encrypt(&key, &counter, plaintext).unwrap();
  /// ```
  pub fn encrypt(
    &self,
    key: &C::Key,
    counter: &Counter<{ C::BLOCK_SIZE / 2 }>,
    plaintext: &[u8],
  ) -> Result<Vec<u8>, String> {
    let mut ciphertext = Vec::new();
    let mut cipher_counter = *counter;

    for chunk in plaintext.chunks(C::BLOCK_SIZE) {
      let mut block = [0u8; C::BLOCK_SIZE];
      block[..C::BLOCK_SIZE / 2].copy_from_slice(&self.nonce);
      block[C::BLOCK_SIZE / 2..].copy_from_slice(&cipher_counter.0);
      cipher_counter.increment()?;

      let encrypted = C::encrypt_block(key, &C::Block::from(block.to_vec()));

      for (x, y) in chunk.iter().zip(encrypted.as_ref()) {
        ciphertext.push(x ^ y);
      }
    }

    Ok(ciphertext)
  }

  /// Decrypt a ciphertext with counter of size [`BlockCipher::BLOCK_SIZE`]/2 bytes
  /// ## Usage
  /// ```
  /// #![allow(incomplete_features)]
  /// #![feature(generic_const_exprs)]
  /// use rand::{thread_rng, Rng};
  /// use ronkathon::encryption::symmetric::{
  ///   aes::{Key, AES},
  ///   counter::Counter,
  ///   modes::ctr::CTR,
  ///   BlockCipher,
  /// };
  ///
  /// let mut rng = thread_rng();
  /// let rand_key: [u8; 16] = rng.gen();
  /// let key = Key::<128>::new(rand_key);
  /// let nonce: [u8; AES::<128>::BLOCK_SIZE / 2] = rng.gen();
  /// let counter: Counter<{ AES::<128>::BLOCK_SIZE / 2 }> = Counter::from(0);
  ///
  /// let ctr = CTR::<AES<128>>::new(nonce);
  /// let plaintext = b"Hello World!";
  ///
  /// let ciphertext = ctr.encrypt(&key, &counter, plaintext).unwrap();
  /// let decrypted = ctr.decrypt(&key, &counter, &ciphertext).unwrap();
  /// ```
  pub fn decrypt(
    &self,
    key: &C::Key,
    counter: &Counter<{ C::BLOCK_SIZE / 2 }>,
    ciphertext: &[u8],
  ) -> Result<Vec<u8>, String> {
    self.encrypt(key, counter, ciphertext)
  }
}

#[cfg(test)]
mod tests {
  use rand::{thread_rng, Rng};
  use rstest::{fixture, rstest};

  use super::*;
  use crate::encryption::symmetric::aes::{Key, AES};

  #[fixture]
  fn rand_key() -> Key<128> {
    let mut rng = thread_rng();
    let rand_key: [u8; 16] = rng.gen();
    Key::new(rand_key)
  }

  fn rand_message(length: usize) -> Vec<u8> {
    let mut rng = thread_rng();

    (0..length).map(|_| rng.gen::<u8>()).collect()
  }

  #[rstest]
  fn ctr(rand_key: Key<128>) {
    for _ in 0..10 {
      let mut rng = thread_rng();
      let nonce: [u8; AES::<128>::BLOCK_SIZE / 2] = rng.gen();
      let counter: Counter<{ AES::<128>::BLOCK_SIZE / 2 }> = Counter::from(0);

      let ctr = CTR::<AES<128>>::new(nonce);

      let plaintext = rand_message(rng.gen_range(1000..10000));
      let ciphertext = ctr.encrypt(&rand_key, &counter, &plaintext).unwrap();

      let decrypted = ctr.decrypt(&rand_key, &counter, &ciphertext).unwrap();

      assert_eq!(plaintext, decrypted);
    }
  }
}
