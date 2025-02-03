//! Contains implementation for Counter (CTR) mode of operation in block ciphers

use crate::encryption::{symmetric::counter::Counter, BlockOperations, Encryption};

/// [`BlockCipher`] counter mode of operation with two parameters:
/// - `C`, a cipher that implements the `BlockCipher` trait.
/// - `M`, a usize const that indicates the size of counter in bytes.
pub struct CTR<C: Encryption + BlockOperations, const M: usize>
where [(); C::BLOCK_SIZE - M]: {
  nonce: [u8; C::BLOCK_SIZE - M],
}

impl<C: Encryption + BlockOperations, const M: usize> CTR<C, M>
where [(); C::BLOCK_SIZE - M]:
{
  /// Create a CTR mode of operation object
  /// # Arguments
  /// - `nonce`: *Non-repeating* IV of [`BlockCipher::BLOCK_SIZE`] - M bytes. Nonce is concatenated
  ///   with [`Counter`], of M bytes, to generate a keystream that does not repeat for a long time.
  pub fn new(nonce: [u8; C::BLOCK_SIZE - M]) -> Self { Self { nonce } }

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
  /// use ronkathon::encryption::{
  ///   symmetric::{
  ///     aes::{Key, AES},
  ///     counter::Counter,
  ///     modes::ctr::CTR,
  ///   },
  ///   BlockOperations,
  /// };
  ///
  /// let mut rng = thread_rng();
  /// let rand_key: [u8; 16] = rng.gen();
  /// let key = Key::<128>::new(rand_key);
  /// let nonce: [u8; 12] = rng.gen();
  /// let counter: Counter<4> = Counter::from(0);
  ///
  /// let ctr = CTR::<AES<128>, 4>::new(nonce);
  /// let plaintext = b"Hello World!";
  ///
  /// let ciphertext = ctr.encrypt(&key, &counter, plaintext).unwrap();
  /// ```
  pub fn encrypt(
    &self,
    key: &C::Key,
    counter: &Counter<M>,
    plaintext: &[u8],
  ) -> Result<Vec<u8>, String> {
    let mut ciphertext = Vec::new();
    let mut cipher_counter = *counter;
    let value = C::new(key.clone());
    for chunk in plaintext.chunks(C::BLOCK_SIZE) {
      let cipher = match value {
        Ok(ref cipher) => cipher,
        Err(_) => panic!("Error creating cipher"),
      };
      let mut block = [0u8; C::BLOCK_SIZE];
      block[..{ C::BLOCK_SIZE - M }].copy_from_slice(&self.nonce);
      block[{ C::BLOCK_SIZE - M }..].copy_from_slice(&cipher_counter.0);
      cipher_counter.increment()?;

      let encrypted = cipher.encrypt_block(C::Block::from(block.to_vec())).unwrap();

      for (x, y) in chunk.iter().zip(encrypted.as_ref()) {
        ciphertext.push(x ^ y);
      }
    }

    Ok(ciphertext)
  }

  /// Decrypt a ciphertext with counter of size [`BlockCipher::BLOCK_SIZE`] - M bytes
  /// ## Usage
  /// ```
  /// #![allow(incomplete_features)]
  /// #![feature(generic_const_exprs)]
  /// use rand::{thread_rng, Rng};
  /// use ronkathon::encryption::{
  ///   symmetric::{
  ///     aes::{Key, AES},
  ///     counter::Counter,
  ///     modes::ctr::CTR,
  ///   },
  ///   BlockOperations,
  /// };
  ///
  /// let mut rng = thread_rng();
  /// let rand_key: [u8; 16] = rng.gen();
  /// let key = Key::<128>::new(rand_key);
  /// let nonce: [u8; 12] = rng.gen();
  /// let counter: Counter<4> = Counter::from(0);
  ///
  /// let ctr = CTR::<AES<128>, 4>::new(nonce);
  /// let plaintext = b"Hello World!";
  ///
  /// let ciphertext = ctr.encrypt(&key, &counter, plaintext).unwrap();
  /// let decrypted = ctr.decrypt(&key, &counter, &ciphertext).unwrap();
  /// ```
  pub fn decrypt(
    &self,
    key: &C::Key,
    counter: &Counter<M>,
    ciphertext: &[u8],
  ) -> Result<Vec<u8>, String> {
    self.encrypt(key, counter, ciphertext)
  }
}

#[cfg(test)]
mod tests {
  use std::{fmt::Write, num::ParseIntError};

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
  fn test_ctr_rand_key(rand_key: Key<128>) {
    for _ in 0..10 {
      let mut rng = thread_rng();
      let nonce: [u8; AES::<128>::BLOCK_SIZE - 4] = rng.gen();
      let counter: Counter<4> = Counter::from(0);

      let ctr = CTR::<AES<128>, 4>::new(nonce);

      let plaintext = rand_message(rng.gen_range(1000..10000));
      let ciphertext = ctr.encrypt(&rand_key, &counter, &plaintext).unwrap();

      let decrypted = ctr.decrypt(&rand_key, &counter, &ciphertext).unwrap();

      assert_eq!(plaintext, decrypted);
    }
  }

  /// Encode bytes to hex
  pub fn encode_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
      write!(&mut s, "{:02x}", b).unwrap();
    }
    s
  }

  /// Decode hex to bytes
  pub fn decode_hex(s: &str) -> Result<Vec<u8>, ParseIntError> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16)).collect()
  }

  // `test_ctr_128`, `test_ctr_192`, and 'test_ctr_256' are based on test vectors given in:
  // "Recommendation for Block Cipher Modes of Operation(NIST Special Publication 800-38A)"
  // Link: (https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38a.pdf)

  // Appendix F.5.1 and F.5.2
  #[rstest]
  #[case(
    "2b7e151628aed2a6abf7158809cf4f3c",
    "f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff",
    "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710",
    "874d6191b620e3261bef6864990db6ce9806f66b7970fdff8617187bb9fffdff5ae4df3edbd5d35e5b4f09020db03eab1e031dda2fbe03d1792170a0f3009cee"
  )]
  fn test_ctr_128(
    #[case] kx: &str,
    #[case] ivx: &str,
    #[case] ptx: &str,
    #[case] expected_ctx: &str,
  ) {
    let k = decode_hex(kx).unwrap();
    let iv = decode_hex(ivx).unwrap();
    let pt = decode_hex(ptx).unwrap();

    let key = Key::<128>::new(k.try_into().unwrap());
    let nonce = &iv[..8];
    let counter = Counter(iv[8..].try_into().unwrap());

    let ctr = CTR::<AES<128>, 8>::new(nonce.try_into().unwrap());

    let ct = ctr.encrypt(&key, &counter, &pt).unwrap();

    let ctx = encode_hex(&ct);
    assert_eq!(ctx, expected_ctx);

    let _pt = ctr.decrypt(&key, &counter, &ct).unwrap();

    let _ptx = encode_hex(&_pt);
    assert_eq!(_ptx, ptx);
  }

  // Appendix F.5.3 and F.5.4
  #[rstest]
  #[case(
    "8e73b0f7da0e6452c810f32b809079e562f8ead2522c6b7b",
    "f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff",
    "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710",
    "1abc932417521ca24f2b0459fe7e6e0b090339ec0aa6faefd5ccc2c6f4ce8e941e36b26bd1ebc670d1bd1d665620abf74f78a7f6d29809585a97daec58c6b050"
  )]
  fn test_ctr_192(
    #[case] kx: &str,
    #[case] ivx: &str,
    #[case] ptx: &str,
    #[case] expected_ctx: &str,
  ) {
    let k = decode_hex(kx).unwrap();
    let iv = decode_hex(ivx).unwrap();
    let pt = decode_hex(ptx).unwrap();

    let key = Key::<192>::new(k.try_into().unwrap());
    let nonce = &iv[..8];
    let counter = Counter(iv[8..].try_into().unwrap());

    let ctr = CTR::<AES<192>, 8>::new(nonce.try_into().unwrap());

    let ct = ctr.encrypt(&key, &counter, &pt).unwrap();

    let ctx = encode_hex(&ct);
    assert_eq!(ctx, expected_ctx);

    let _pt = ctr.decrypt(&key, &counter, &ct).unwrap();

    let _ptx = encode_hex(&_pt);
    assert_eq!(_ptx, ptx);
  }

  // Appendix F.5.3 and F.5.4
  #[rstest]
  #[case(
    "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4",
    "f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff",
    "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710",
    "601ec313775789a5b7a7f504bbf3d228f443e3ca4d62b59aca84e990cacaf5c52b0930daa23de94ce87017ba2d84988ddfc9c58db67aada613c2dd08457941a6"
  )]
  fn test_ctr_256(
    #[case] kx: &str,
    #[case] ivx: &str,
    #[case] ptx: &str,
    #[case] expected_ctx: &str,
  ) {
    let k = decode_hex(kx).unwrap();
    let iv = decode_hex(ivx).unwrap();
    let pt = decode_hex(ptx).unwrap();

    let key = Key::<256>::new(k.try_into().unwrap());
    let nonce = &iv[..8];
    let counter = Counter(iv[8..].try_into().unwrap());

    let ctr = CTR::<AES<256>, 8>::new(nonce.try_into().unwrap());

    let ct = ctr.encrypt(&key, &counter, &pt).unwrap();

    let ctx = encode_hex(&ct);
    assert_eq!(ctx, expected_ctx);

    let _pt = ctr.decrypt(&key, &counter, &ct).unwrap();

    let _ptx = encode_hex(&_pt);
    assert_eq!(_ptx, ptx);
  }
}
