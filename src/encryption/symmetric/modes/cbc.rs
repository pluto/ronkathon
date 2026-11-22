//! Cipher block chaining mode of operation for [`BlockCipher`]
use crate::encryption::{BlockOperations, Encryption};

/// Cipher block chaining mode of operation that works on any [`BlockCipher`]. Initialisation
/// Vector (IV) should not be reused for different plaintext.
pub struct CBC<C: Encryption + BlockOperations> {
  iv: C::Block,
}

fn xor_blocks(a: &mut [u8], b: &[u8]) {
  for (x, y) in a.iter_mut().zip(b) {
    *x ^= *y;
  }
}

impl<C: Encryption + BlockOperations> CBC<C> {
  /// creates a new [`CBC`] mode of operation for [`BlockCipher`]
  /// ## Arguments
  /// - `iv`: initialisation vector for randomising the state.
  ///
  /// Note: IV shouldn't be reused for different encryptions
  pub fn new(iv: C::Block) -> Self { Self { iv } }

  /// Encrypt arbitrary length of bytes.
  ///
  /// ## Arguments
  /// - `key`: cipher's secret key
  /// - `plaintext`: data to encrypt
  ///
  /// ## Usage
  /// ```
  /// #![allow(incomplete_features)]
  /// #![feature(generic_const_exprs)]
  /// use rand::{thread_rng, Rng};
  /// use ronkathon::encryption::symmetric::{
  ///   aes::{Block, Key, AES},
  ///   modes::cbc::CBC,
  /// };
  ///
  /// let mut rng = thread_rng();
  /// let rand_key: [u8; 16] = rng.gen();
  /// let key = Key::<128>::new(rand_key);
  /// let iv = Block(rng.gen());
  /// let plaintext = b"Hello World!";
  ///
  /// let cbc = CBC::<AES<128>>::new(iv);
  ///
  /// let ciphertext = cbc.encrypt(&key, plaintext);
  /// ```
  ///
  /// **Note**: plaintext is always padded using PKCS#7, so the ciphertext is one to
  /// [`BlockCipher::BLOCK_SIZE`] bytes longer than the plaintext. A plaintext that is already a
  /// multiple of the block size gets a full block of padding, so that [`CBC::decrypt`] can always
  /// tell the padding apart from the message.
  pub fn encrypt(&self, key: &C::Key, plaintext: &[u8]) -> Vec<u8> {
    let mut ciphertext = Vec::new();
    let mut prev_ciphertext = self.iv;

    // pad plaintext using PKCS#7 padding scheme: `n` bytes of value `n`, where `n` is between 1 and
    // the block size
    let mut plaintext = plaintext.to_vec();
    let length = C::BLOCK_SIZE - (plaintext.len() % C::BLOCK_SIZE);
    plaintext.extend(std::iter::repeat(length as u8).take(length));
    let value = C::new(key.clone());
    for chunk in plaintext.chunks(C::BLOCK_SIZE) {
      let cipher = match value {
        Ok(ref cipher) => cipher,
        Err(_) => panic!("Error creating cipher"),
      };
      xor_blocks(prev_ciphertext.as_mut(), chunk);
      prev_ciphertext = cipher.encrypt_block(prev_ciphertext).unwrap();
      ciphertext.extend_from_slice(prev_ciphertext.as_ref());
    }
    ciphertext
  }

  /// Decrypt ciphertext using CBC mode.
  ///
  /// ## Arguments
  /// - `key`: secret key used during encryption
  /// - `ciphertext`: plaintext encrypted using key and iv
  ///
  /// ## Usage
  /// ```
  /// #![allow(incomplete_features)]
  /// #![feature(generic_const_exprs)]
  /// use rand::{thread_rng, Rng};
  /// use ronkathon::encryption::symmetric::{
  ///   aes::{Block, Key, AES},
  ///   modes::cbc::CBC,
  /// };
  ///
  /// let mut rng = thread_rng();
  /// let rand_key: [u8; 16] = rng.gen();
  /// let key = Key::<128>::new(rand_key);
  /// let iv = Block(rng.gen());
  /// let plaintext = b"Hello World!";
  ///
  /// let cbc = CBC::<AES<128>>::new(iv);
  ///
  /// let ciphertext = cbc.encrypt(&key, plaintext);
  /// let decrypted = cbc.decrypt(&key, &ciphertext);
  ///
  /// assert_eq!(plaintext.as_slice(), decrypted);
  /// ```
  ///
  /// **Note**: the PKCS#7 padding added by [`CBC::encrypt`] is removed, so the original plaintext
  /// is returned. Panics if the ciphertext doesn't end in valid padding, e.g. because it was
  /// decrypted with the wrong key or IV.
  pub fn decrypt(&self, key: &C::Key, ciphertext: &[u8]) -> Vec<u8> {
    assert!(ciphertext.len() % C::BLOCK_SIZE == 0, "ciphertext is not a multiple of block size");

    let mut prev_ciphertext: Vec<u8> = self.iv.as_ref().to_vec();
    let mut plaintext = Vec::new();

    let value = C::new(key.clone());
    for chunk in ciphertext.chunks(C::BLOCK_SIZE) {
      let cipher = match value {
        Ok(ref cipher) => cipher,
        Err(_) => panic!("Error creating cipher"),
      };
      let mut decrypted = cipher.decrypt_block(C::Block::from(chunk.to_vec())).unwrap();
      xor_blocks(decrypted.as_mut(), &prev_ciphertext);
      prev_ciphertext = chunk.to_vec();

      plaintext.extend_from_slice(decrypted.as_ref());
    }

    // remove PKCS#7 padding: the last byte gives the padding length `n`, and all of the last `n`
    // bytes must be equal to `n`
    let length = plaintext.last().copied().unwrap_or(0) as usize;
    assert!(
      (1..=C::BLOCK_SIZE).contains(&length)
        && plaintext[plaintext.len() - length..].iter().all(|&byte| byte as usize == length),
      "invalid PKCS#7 padding"
    );
    plaintext.truncate(plaintext.len() - length);

    plaintext
  }
}

#[cfg(test)]
mod tests {
  use rand::{thread_rng, Rng};
  use rstest::{fixture, rstest};

  use super::*;
  use crate::encryption::symmetric::aes::{Block, Key, AES};

  #[fixture]
  fn rand_key() -> Key<128> {
    let mut rng = thread_rng();
    let rand_key: [u8; 16] = rng.gen();
    Key::new(rand_key)
  }

  #[fixture]
  fn rand_iv() -> Block {
    let mut rng = thread_rng();
    Block(rng.gen())
  }

  fn rand_message(length: usize) -> Vec<u8> {
    let mut rng = thread_rng();

    (0..length).map(|_| rng.gen::<u8>()).collect()
  }

  #[rstest]
  fn cbc(rand_key: Key<128>, rand_iv: Block) {
    let cbc = CBC::<AES<128>>::new(rand_iv);

    for _ in 0..10 {
      let mut rng = thread_rng();
      let plaintext = rand_message(rng.gen_range(1000..10000));
      let ciphertext = cbc.encrypt(&rand_key, &plaintext);

      let decrypted = cbc.decrypt(&rand_key, &ciphertext);

      assert_eq!(plaintext.len(), decrypted.len());
      assert_eq!(plaintext, decrypted);
    }
  }

  /// Every length from empty to three blocks, so that both partial and full blocks of padding
  /// are covered.
  #[rstest]
  fn every_length_round_trips(rand_key: Key<128>, rand_iv: Block) {
    let cbc = CBC::<AES<128>>::new(rand_iv);

    for length in 0..=48 {
      let plaintext = rand_message(length);
      let ciphertext = cbc.encrypt(&rand_key, &plaintext);

      assert_eq!(ciphertext.len(), (length / 16 + 1) * 16);
      assert_eq!(cbc.decrypt(&rand_key, &ciphertext), plaintext);
    }
  }

  /// A block-aligned message whose end looks like padding (`0x01`) or like no valid padding at
  /// all (`0x00`) must come back unchanged. Random messages hit these cases now and then (#218).
  #[rstest]
  #[case::ends_in_one(0x01)]
  #[case::ends_in_zero(0x00)]
  #[case::ends_in_large_byte(0xff)]
  fn aligned_message_round_trips(rand_key: Key<128>, rand_iv: Block, #[case] last_byte: u8) {
    let cbc = CBC::<AES<128>>::new(rand_iv);

    let mut plaintext = rand_message(32);
    plaintext[31] = last_byte;

    let ciphertext = cbc.encrypt(&rand_key, &plaintext);
    assert_eq!(cbc.decrypt(&rand_key, &ciphertext), plaintext);
  }

  #[rstest]
  #[should_panic(expected = "invalid PKCS#7 padding")]
  fn wrong_iv_panics_on_padding(rand_key: Key<128>, rand_iv: Block) {
    let cbc = CBC::<AES<128>>::new(rand_iv);
    let ciphertext = cbc.encrypt(&rand_key, b"Hello World!");

    // the last byte of the last block decides the padding length, so flip the IV byte that
    // lands on it after decryption of a single block
    let mut wrong_iv = rand_iv;
    wrong_iv.0[15] ^= 0xff;
    CBC::<AES<128>>::new(wrong_iv).decrypt(&rand_key, &ciphertext);
  }

  #[rstest]
  fn different_iv(rand_key: Key<128>, rand_iv: Block) {
    let cbc = CBC::<AES<128>>::new(rand_iv);

    let mut rand_iv = rand_iv;
    rand_iv.0[0] += 1;

    let cbc2 = CBC::<AES<128>>::new(rand_iv);

    let mut rng = thread_rng();
    let plaintext = rand_message(rng.gen_range(1000..100000));

    let ciphertext = cbc.encrypt(&rand_key, &plaintext);
    let ciphertext2 = cbc2.encrypt(&rand_key, &plaintext);

    assert_ne!(ciphertext, ciphertext2);

    let decrypted = cbc.decrypt(&rand_key, &ciphertext);
    let decrypted2 = cbc2.decrypt(&rand_key, &ciphertext2);

    assert_eq!(plaintext, decrypted);
    assert_eq!(decrypted, decrypted2);
  }
}
