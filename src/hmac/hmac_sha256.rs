//! An implementation of the HMAC using the SHA-256 hash function.

use crate::hashes::sha::Sha256;

const SHA256_BLOCK_SIZE: usize = 64;
const SHA256_OUTPUT_SIZE: usize = 32;

/// Computes a block-sized key from the given key.
///
/// If the key is longer than the block size, it is hashed and the result is truncated.
/// Otherwise, the key is padded with zeros to fit the block size.
fn compute_block_sized_key(key: &[u8]) -> [u8; SHA256_BLOCK_SIZE] {
  let mut block_sized_key = [0; SHA256_BLOCK_SIZE];

  if key.len() > SHA256_BLOCK_SIZE {
    // Hash the key and use only the first SHA256_BLOCK_SIZE bytes
    let hashfunc = Sha256::new();
    let digest = hashfunc.digest(key);
    block_sized_key[..SHA256_OUTPUT_SIZE].copy_from_slice(&digest);
  } else {
    // Copy the key directly, padded with zeros if necessary
    block_sized_key[..key.len()].copy_from_slice(key);
  }

  block_sized_key
}

/// Computes the HMAC of the given key and message using the SHA-256 hash function.
///
/// # Arguments
///
/// * `key` - The secret key used for HMAC.
/// * `message` - The message to authenticate.
///
/// # Returns
///
/// Returns a 32-byte HMAC-SHA256 digest.
///
/// # Example
///
/// ```
/// use hex;
/// use ronkathon::hmac::hmac_sha256::hmac_sha256;
///
/// let key = b"supersecretkey";
/// let message = b"message";
/// assert_eq!(
///   hex::encode(hmac_sha256(key, message)),
///   "1e46048d8b12509a93f36926f77c369a8520aa03923f854a8174bb58756cd68a"
/// );
/// ```
pub fn hmac_sha256(key: &[u8], message: &[u8]) -> [u8; SHA256_OUTPUT_SIZE] {
  let block_sized_key = compute_block_sized_key(key);

  let mut o_key_pad = [0; SHA256_BLOCK_SIZE];
  let mut i_key_pad = [0; SHA256_BLOCK_SIZE];
  for i in 0..SHA256_BLOCK_SIZE {
    o_key_pad[i] = block_sized_key[i] ^ 0x5c;
    i_key_pad[i] = block_sized_key[i] ^ 0x36;
  }

  // Compute the inner hash: H((K ⊕ ipad) | message)
  let mut inner_hash_input = Vec::with_capacity(SHA256_BLOCK_SIZE + message.len());
  inner_hash_input.extend_from_slice(&i_key_pad);
  inner_hash_input.extend_from_slice(message);
  let hashfunc = Sha256::new();
  let inner_hash = hashfunc.digest(&inner_hash_input);

  // Compute the outer hash: H((K ⊕ opad) | inner_hash)
  let mut outer_hash_input = Vec::with_capacity(SHA256_BLOCK_SIZE + SHA256_OUTPUT_SIZE);
  outer_hash_input.extend_from_slice(&o_key_pad);
  outer_hash_input.extend_from_slice(&inner_hash);
  hashfunc.digest(&outer_hash_input).try_into().unwrap()
}

#[cfg(test)]
mod tests {
  // Test gotten from the standard https://datatracker.ietf.org/doc/html/rfc4231#section-4

  use rstest::rstest;

  use super::*;
  #[rstest]
  #[case(
    "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b",
    "4869205468657265",
    "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
  )]
  #[case(
    "4a656665",
    "7768617420646f2079612077616e7420666f72206e6f7468696e673f",
    "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
  )]
  #[case("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
  "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe")]
  #[case("0102030405060708090a0b0c0d0e0f10111213141516171819", "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd",
  "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b")]
  #[case(
    "0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c",
    "546573742057697468205472756e636174696f6e",
    "a3b6167473100ee06e0c796c2955552bfa6f7c0a6a8aef8b93f860aab0cd20c5"
  )]
  #[case("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374",
  "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54")]
  #[case("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "5468697320697320612074657374207573696e672061206c6172676572207468616e20626c6f636b2d73697a65206b657920616e642061206c6172676572207468616e20626c6f636b2d73697a6520646174612e20546865206b6579206e6565647320746f20626520686173686564206265666f7265206265696e6720757365642062792074686520484d414320616c676f726974686d2e",
  "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2")]
  fn test_hmac_sha256(#[case] key: &str, #[case] message: &str, #[case] expected: &str) {
    let key = hex::decode(key).expect("Invalid hex key");
    let message = hex::decode(message).expect("Invalid hex message");

    assert_eq!(hex::encode(hmac_sha256(&key, &message)), expected);
  }
}
