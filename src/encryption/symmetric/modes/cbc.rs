//! Cipher block chaining mode of operation for [`BlockCipher`]
use crate::encryption::symmetric::BlockCipher;

/// Cipher block chaining mode of operation that works on any [`BlockCipher`]. Initialisation
/// Vector (IV) should not be reused for different plaintext.
pub struct CBC<C: BlockCipher> {
  iv: C::Block,
}

fn xor_blocks<'a>(a: &mut [u8], b: &[u8]) {
  for (x, y) in a.iter_mut().zip(b) {
    *x ^= *y;
  }
}

impl<C: BlockCipher> CBC<C> {
  pub fn new(iv: C::Block) -> Self { Self { iv } }

  pub fn encrypt(&self, key: &C::Key, plaintext: &[u8]) -> Vec<u8> {
    let block_size = self.iv.as_ref().len();
    let mut ciphertext = Vec::new();
    let mut prev_ciphertext = self.iv;

    // pad plaintext by adding nul bytes if not a multiple of blocks
    let mut plaintext = plaintext.to_vec();
    plaintext.extend(std::iter::repeat(b"\0"[0]).take(block_size - (plaintext.len() % block_size)));

    for chunk in plaintext.chunks(block_size) {
      xor_blocks(prev_ciphertext.as_mut(), chunk);
      prev_ciphertext = C::encrypt(key, &C::Block::from(chunk.to_vec()));
      ciphertext.extend_from_slice(prev_ciphertext.as_ref());
    }
    ciphertext
  }

  pub fn decrypt(&self, key: &C::Key, ciphertext: &[u8]) -> Vec<u8> {
    let block_size = self.iv.as_ref().len();

    assert!(ciphertext.len() % block_size == 0, "ciphertext is not a multiple of block size");

    let mut prev_ciphertext: Vec<u8> = self.iv.as_ref().to_vec();
    let mut plaintext = Vec::new();

    for chunk in ciphertext.chunks(block_size) {
      let mut decrypted = C::decrypt(key, &C::Block::from(chunk.to_vec()));
      xor_blocks(decrypted.as_mut(), &prev_ciphertext);
      prev_ciphertext = chunk.to_vec();

      plaintext.extend_from_slice(decrypted.as_ref());
    }

    plaintext
  }
}

#[cfg(test)]
mod tests {
  use rand::{thread_rng, Rng};

  use super::*;
  use crate::encryption::symmetric::aes::{Block, Key, AES};

  #[test]
  fn cbc() {
    let mut rng = thread_rng();
    let rand_key: [u8; 16] = rng.gen();
    let key: Key<128> = Key::new(rand_key);

    let iv: [u8; 16] = rng.gen();

    let cbc = CBC::<AES<128>>::new(Block(iv));

    let plaintext = b"hello world!";

    let ciphertext = cbc.encrypt(&key, plaintext);

    let decrypted = cbc.decrypt(&key, &ciphertext);

    println!("plaintext: {:?}\nciphertext: {:?}", plaintext, decrypted);
  }
}
