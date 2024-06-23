//! Contains implementation of DES encryption

pub mod constants;
#[cfg(test)] pub mod tests;
use constants::*;

/// Block represents 64-bit sized data
pub type Block = [u8; 8];
/// Subkey represents 48-bit round keys used in each round of the encryption
pub type Subkey = [u8; 6];

// pub trait BlockCipher {}

/// DES encryption
#[derive(Debug)]
pub struct Des {
  /// round keys
  subkeys: [Subkey; 16],
}

/// combine bits in first bit of `u8` into a u8
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

fn rotate_left_28(input: u32, shift: usize) -> u32 {
  let mask = (1 << 28) - 1; // Mask to keep only the lowest 28 bits
  ((input << shift) & mask) | (input >> (28 - shift))
}

/// left shifts a 28-bit number represented in big-endian to left by `shift` positions
/// ## Example
/// - `100000025`: `00000101 11110101 11100001 00011001`
/// - shift by 2 positions -> `00000111 11010111 10000100 01100101`
fn left_shift(input: &[u8], shift: usize) -> Vec<u8> {
  assert!(input.len() == 4);
  let input: [u8; 4] = [input[0], input[1], input[2], input[3]];
  let input_u = u32::from_be_bytes(input);
  let rotated_bits = rotate_left_28(input_u, shift);
  let output = rotated_bits.to_be_bytes();
  output.to_vec()
}

impl Des {
  /// create a DES encryption function with round subkeys
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

    // split permuted 56 bits into 28 bits
    let (mut left, mut right) = (vec![0u8; 4], vec![0u8; 4]);
    for i in 0..28 {
      if permuted_bits[i] == 1 {
        left[i / 8] |= 1 << (7 - ((i + 4) % 8));
      }
      if permuted_bits[i + 28] == 1 {
        right[i / 8] |= 1 << (7 - ((i + 4) % 8));
      }
    }

    let mut subkeys = [[0u8; 6]; 16];

    for i in 0..16 {
      // shift left and right parts
      left = left_shift(&left, SHIFTS[i]);
      right = left_shift(&right, SHIFTS[i]);

      // combine and permute bits
      let left_u = u32::from_be_bytes([left[0], left[1], left[2], left[3]]);
      let right_u = u32::from_be_bytes([right[0], right[1], right[2], right[3]]);
      let combined: u64 = ((left_u as u64) << 28) | right_u as u64;
      // let combined = [left.clone(), right.clone()].concat();
      let combined = combined.to_be_bytes();

      let permuted = Self::permute(&combined[1..], &PC2);

      for j in 0..6 {
        subkeys[i][j] = get_byte_from_bits(&permuted[j * 8..(j + 1) * 8]);
      }
    }

    subkeys
  }

  fn expansion(data: &[u8; 4]) -> [u8; 6] {
    let permuted_bits = Self::permute(data, &E);
    permuted_bits
      .chunks_exact(8)
      .map(get_byte_from_bits)
      .collect::<Vec<u8>>()
      .try_into()
      .unwrap_or_else(|v: Vec<u8>| panic!("expected vec of len: {} but got: {}", 6, v.len()))
  }

  fn feistel_mix(state: [u8; 6], subkey: [u8; 6]) -> [u8; 8] {
    let input = state.into_iter().zip(subkey).map(|(a, b)| a ^ b).collect::<Vec<u8>>();

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

  fn mix(state: [u8; 4], subkey: [u8; 4]) -> [u8; 4] {
    state
      .into_iter()
      .zip(subkey)
      .map(|(a, b)| a ^ b)
      .collect::<Vec<u8>>()
      .try_into()
      .unwrap_or_else(|v: Vec<u8>| panic!("Expected vec of len: {} but got {}", 4, v.len()))
  }

  fn substitution(substate: [u8; 8]) -> [u8; 4] {
    let mut output = [0u8; 4];

    for (i, entry) in substate.iter().enumerate() {
      let row = ((entry & 0b100000) >> 4) | (entry & 1);
      let column = (entry >> 1) & 0b1111;
      let s_box_value = S_BOXES[i][row as usize][column as usize];

      let bit_pos = i * 4;
      output[i / 2] |= s_box_value << (4 - (bit_pos % 8));
    }

    output
  }

  fn feistel_permutation(data: &[u8; 4]) -> [u8; 4] {
    Self::permute(data, &P_F)
      .chunks_exact(8)
      .map(get_byte_from_bits)
      .collect::<Vec<u8>>()
      .try_into()
      .unwrap_or_else(|v: Vec<u8>| panic!("expected vec of len: {} but got: {}", 4, v.len()))
  }

  fn feistel_function(right: &[u8; 4], subkey: Subkey) -> [u8; 4] {
    let expanded = Self::expansion(right);
    let mixed = Self::feistel_mix(expanded, subkey);
    let substituted = Self::substitution(mixed);
    Self::feistel_permutation(&substituted)
  }

  fn initial_permutation(data: &Block) -> Block {
    Self::permute(data, &IP)
      .chunks_exact(8)
      .map(get_byte_from_bits)
      .collect::<Vec<u8>>()
      .try_into()
      .unwrap_or_else(|v: Vec<u8>| panic!("expected vec of len: {} but got: {}", 8, v.len()))
  }

  fn final_permutation(data: &Block) -> Block {
    Self::permute(data, &FP)
      .chunks_exact(8)
      .map(get_byte_from_bits)
      .collect::<Vec<u8>>()
      .try_into()
      .unwrap_or_else(|v: Vec<u8>| panic!("Expected vec of len: {} but got: {}", 8, v.len()))
  }

  /// Encrypt a message of size [`Block`]
  pub fn encrypt(&self, message: &Block) -> Block {
    let permuted_bits = Self::initial_permutation(message);

    let (mut left, mut right) =
      ([permuted_bits[0], permuted_bits[1], permuted_bits[2], permuted_bits[3]], [
        permuted_bits[4],
        permuted_bits[5],
        permuted_bits[6],
        permuted_bits[7],
      ]);

    for i in 0..16 {
      let temp = right;
      right = Self::mix(left, Self::feistel_function(&right, self.subkeys[i]));
      left = temp;
    }

    let cipher: Block = [right, left]
      .concat()
      .try_into()
      .unwrap_or_else(|v: Vec<u8>| panic!("Expected vec of len: {} but got: {}", 8, v.len()));

    Self::final_permutation(&cipher)
  }

  /// Decrypt a ciphertext of size [`Block`]
  pub fn decrypt(&self, ciphertext: &Block) -> Block {
    let permuted_bits = Self::initial_permutation(ciphertext);
    let (mut left, mut right) =
      ([permuted_bits[0], permuted_bits[1], permuted_bits[2], permuted_bits[3]], [
        permuted_bits[4],
        permuted_bits[5],
        permuted_bits[6],
        permuted_bits[7],
      ]);

    for i in (0..16).rev() {
      let temp = right;
      right = Self::mix(left, Self::feistel_function(&right, self.subkeys[i]));
      left = temp;
    }

    let cipher: Block = [right, left]
      .concat()
      .try_into()
      .unwrap_or_else(|v: Vec<u8>| panic!("Expected vec of len: {} but got: {}", 8, v.len()));

    Self::final_permutation(&cipher)
  }
}
