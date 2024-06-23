//! Contains implementation of DES encryption
#[doc = include_str!("./README.md")]
#[cfg(test)]
pub mod tests;

pub mod constants;
use constants::*;

/// Block represents 64-bit sized data
pub type Block = [u8; 8];
/// 32-bit sized half blocks
pub type HalfBlock = [u8; 4];

/// Subkey represents 48-bit round keys used in each round of the encryption
pub type Subkey = [u8; 6];

// pub trait BlockCipher {}

/// DES encryption
#[derive(Debug)]
pub struct DES {
  /// round keys
  subkeys: [Subkey; 16],
}

/// combine bits in first bit of `u8` into a u8
#[inline(always)]
fn get_byte_from_bits(bits: &[u8]) -> u8 {
  debug_assert_eq!(bits.len(), 8);
  bits[0] << 7
    | bits[1] << 6
    | bits[2] << 5
    | bits[3] << 4
    | bits[4] << 3
    | bits[5] << 2
    | bits[6] << 1
    | bits[7]
}

#[inline(always)]
fn rotate_left_28(input: u32, shift: usize) -> u32 {
  let mask = (1 << 28) - 1; // Mask to keep only the lowest 28 bits
  ((input << shift) & mask) | (input >> (28 - shift))
}

/// left shifts a 28-bit number represented in big-endian to left by `shift` positions
/// ## Example
/// - `100000025`: `00000101 11110101 11100001 00011001`
/// - shift by 2 positions -> `00000111 11010111 10000100 01100101`
#[inline(always)]
fn left_shift(input: &[u8], shift: usize) -> [u8; 4] {
  assert!(input.len() == 4);

  let input_u = u32::from_be_bytes([input[0], input[1], input[2], input[3]]);

  rotate_left_28(input_u, shift).to_be_bytes()
}

impl DES {
  /// create a DES encryption function with round subkeys
  /// ## Example
  /// ```rust
  /// use rand::{thread_rng, Rng};
  /// use ronkathon::primitives::symmetric::encryption::des::DES;
  /// let mut rng = thread_rng();
  /// let secret_key = rng.gen();
  ///
  /// let des = DES::new(secret_key);
  pub fn new(secret_key: Block) -> Self { Self { subkeys: Self::generate_subkeys(secret_key) } }

  fn permute(data: &[u8], permutation_table: &[usize]) -> Vec<u8> {
    permutation_table.iter().map(|&i| (data[(i - 1) / 8] >> (7 - (i - 1) % 8)) & 1).collect()
  }

  /// key schedule algorithm to generate round keys.
  /// ## Input
  /// - `key`: 64-bit secret key of the encryption algorithm
  /// ## Output
  /// - `subkeys`: 16 48-bit subkeys for each round
  fn generate_subkeys(key: Block) -> [Subkey; 16] {
    // permute 64 bit key into 56 bits
    let permuted_bits = Self::permute(&key, &PC1);

    // split permuted 56 bits in little-endian order into 28 bits in big-endian
    let (mut left, mut right) = ([0u8; 4], [0u8; 4]);
    for i in 0..28 {
      // left[3-(i/8)] indicates bits in big-endian order
      //
      // since left, right are 4 limbs of 8, and 28-bits are required, thus (i+4) ensures that we
      // keep most significant 4 bits as zero
      if permuted_bits[i] == 1 {
        left[3 - (i / 8)] |= 1 << (7 - ((i + 4) % 8));
      }
      if permuted_bits[i + 28] == 1 {
        right[3 - (i / 8)] |= 1 << (7 - ((i + 4) % 8));
      }
    }

    let mut subkeys = [[0u8; 6]; 16];

    // create subkeys for 16 rounds
    for i in 0..16 {
      // shift left and right parts
      left = left_shift(&left, SHIFTS[i]);
      right = left_shift(&right, SHIFTS[i]);

      // convert to u32
      let left_u = u32::from_be_bytes([left[0], left[1], left[2], left[3]]);
      let right_u = u32::from_be_bytes([right[0], right[1], right[2], right[3]]);

      // combine left and right as 28 bits with left being more significant
      let combined = ((left_u as u64) << 28) | right_u as u64;
      let combined = combined.to_be_bytes();

      // reduce 64-bit combine to 56-bit key length by removing most significant byte
      let permuted = Self::permute(&combined[1..], &PC2);

      for j in 0..6 {
        subkeys[i][j] = get_byte_from_bits(&permuted[j * 8..(j + 1) * 8]);
      }
    }

    subkeys
  }

  /// mixes two element together using xor and divides 48-bit intermediate state into 8 6-bit
  /// elements
  fn feistel_mix(state: [u8; 6], subkey: &Subkey) -> Block {
    let input = state.into_iter().zip(subkey).map(|(a, b)| a ^ b).collect::<Vec<u8>>();

    // divide into 8 6-bit elements
    let mut result = [0u8; 8];
    result[0] = (input[0] >> 2) & 0x3F;
    result[1] = ((input[0] & 0x03) << 4) | ((input[1] >> 4) & 0x0F);
    result[2] = ((input[1] & 0x0F) << 2) | ((input[2] >> 6) & 0x03);
    result[3] = input[2] & 0x3F;
    result[4] = (input[3] >> 2) & 0x3F;
    result[5] = ((input[3] & 0x03) << 4) | ((input[4] >> 4) & 0x0F);
    result[6] = ((input[4] & 0x0F) << 2) | ((input[5] >> 6) & 0x03);
    result[7] = input[5] & 0x3F;
    result
  }

  fn substitution(data: Block) -> HalfBlock {
    let mut output = [0u8; 4];

    for (i, entry) in data.iter().enumerate() {
      let row = ((entry & 0b100000) >> 4) | (entry & 1);
      let column = (entry >> 1) & 0b1111;
      let s_box_value = S_BOXES[i][row as usize][column as usize];

      let bit_pos = i * 4;
      output[i / 2] |= s_box_value << (4 - (bit_pos % 8));
    }

    output
  }

  fn feistel_function(data: &HalfBlock, subkey: &Subkey) -> HalfBlock {
    let expanded = Self::permutation(data, &E);
    let mixed = Self::feistel_mix(expanded, subkey);
    let substituted = Self::substitution(mixed);
    Self::permutation(&substituted, &F_P)
  }

  fn permutation<const N1: usize, const N2: usize>(
    data: &[u8; N1],
    lookup_table: &[usize],
  ) -> [u8; N2] {
    Self::permute(data, lookup_table)
      .chunks_exact(8)
      .map(get_byte_from_bits)
      .collect::<Vec<u8>>()
      .try_into()
      .unwrap_or_else(|v: Vec<u8>| panic!("expected vec of len: {} but got: {}", N2, v.len()))
  }

  fn mix(state: HalfBlock, subkey: HalfBlock) -> HalfBlock {
    state
      .into_iter()
      .zip(subkey)
      .map(|(a, b)| a ^ b)
      .collect::<Vec<u8>>()
      .try_into()
      .unwrap_or_else(|v: Vec<u8>| panic!("Expected vec of len: {} but got {}", 4, v.len()))
  }

  fn des<'a>(data: &Block, subkeys: impl Iterator<Item = &'a Subkey>) -> Block {
    // initial permutation
    let ip: [u8; 8] = Self::permutation(data, &IP);

    // split 64-bit block into 2 32-bit blocks
    let (mut left, mut right) = ([ip[0], ip[1], ip[2], ip[3]], [ip[4], ip[5], ip[6], ip[7]]);

    // 16 rounds
    for subkey in subkeys.into_iter() {
      // swap right and left
      let temp = right;
      // mix right with round subkey
      right = Self::mix(left, Self::feistel_function(&right, subkey));
      left = temp;
    }

    // final round doesn't swap elements, so we swap back
    let combined: Block = [right, left]
      .concat()
      .try_into()
      .unwrap_or_else(|v: Vec<u8>| panic!("Expected vec of len: {} but got: {}", 8, v.len()));

    // final permutation
    Self::permutation(&combined, &FP)
  }

  /// Encrypt a message of size [`Block`]
  ///
  /// ## Example
  /// ```rust
  /// use rand::{thread_rng, Rng};
  /// use ronkathon::primitives::symmetric::encryption::des::DES;
  /// let mut rng = thread_rng();
  /// let secret_key = rng.gen();
  ///
  /// let des = DES::new(secret_key);
  ///
  /// let message = rng.gen();
  /// let encrypted = des.encrypt(&message);
  /// ```
  pub fn encrypt(&self, message: &Block) -> Block { Self::des(message, self.subkeys.iter()) }

  /// Decrypt a ciphertext of size [`Block`]
  ///
  /// ## Example
  /// ```rust
  /// use rand::{thread_rng, Rng};
  /// use ronkathon::primitives::symmetric::encryption::des::DES;
  /// let mut rng = thread_rng();
  /// let secret_key = rng.gen();
  ///
  /// let des = DES::new(secret_key);
  ///
  /// let message = rng.gen();
  /// let encrypted = des.encrypt(&message);
  /// let decrypted = des.decrypt(&encrypted);
  /// ```
  pub fn decrypt(&self, ciphertext: &Block) -> Block {
    Self::des(ciphertext, self.subkeys.iter().rev())
  }
}
