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
  #[allow(unused)]
  /// secret key
  key:     Block,
  /// round keys
  subkeys: [Subkey; 16],
}

/// combine bits in first bit of `u8` into a u8
fn get_byte_from_bits(bits: &[u8]) -> u8 {
  bits[0]
    | bits[1] << 1
    | bits[2] << 2
    | bits[3] << 3
    | bits[4] << 4
    | bits[5] << 5
    | bits[6] << 6
    | bits[7] << 7
}

fn left_shift(input: &[u8], shift: usize) -> Vec<u8> {
  let n = input.len() * 8;
  let mut output = vec![0u8; input.len()];

  for i in 0..n {
    let bit = (input[i / 8] >> (7 - (i % 8))) & 1;
    let new_pos = (i + n - shift) % n;
    if bit == 1 {
      output[new_pos / 8] |= 1 << (7 - (new_pos % 8));
    }
  }
  output
}

impl Des {
  /// create a DES encryption function with round subkeys
  pub fn new(secret_key: Block) -> Self {
    Self { key: secret_key, subkeys: Self::generate_subkeys(secret_key) }
  }

  fn permute(data: &[u8], permutation_table: &[usize]) -> Vec<u8> {
    permutation_table.iter().map(|&i| (data[(i - 1) / 8] >> ((i - 1) % 8)) & 1).collect()
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
        left[i / 8] |= 1 << ((i) % 8);
      }
      if permuted_bits[i + 28] == 1 {
        right[i / 8] |= 1 << ((i) % 8);
      }
    }

    let mut subkeys = [[0u8; 6]; 16];

    for i in 0..16 {
      // shift left and right parts
      left = left_shift(&left, SHIFTS[i]);
      right = left_shift(&right, SHIFTS[i]);

      // combine and permute bits
      let combined = [left.clone(), right.clone()].concat();
      let permuted = Self::permute(&combined, &PC2);

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

  fn mix(state: [u8; 6], subkey: [u8; 6]) -> [u8; 8] {
    let mixed = state.into_iter().zip(subkey).map(|(a, b)| a ^ b).collect::<Vec<u8>>();

    let mut res = [0u8; 8];
    res[0] = mixed[0] & 0x3F; // first 6 bits
    res[1] = (mixed[1] & 0x0F) << 4 | (mixed[0] >> 6); // 4 bits for second and 2 bits from first
    res[2] = (mixed[2] & 0x03) << 4 | (mixed[1] >> 4); // 2 bits from third and 4 bits from second
    res[3] = mixed[2] >> 2; // first 6 bits from third;
    res[4] = mixed[3] & 0x3F; // first 6 bits from fourth
    res[5] = (mixed[4] & 0x0F) << 4 | (mixed[3] >> 6); // 4 bits from fifth and 2 bits from fourth
    res[6] = (mixed[5] & 0x03) << 4 | (mixed[4] >> 4); // 2 bits from sixth and 4 bits from fifth
    res[7] = mixed[5] >> 2;
    res
  }

  fn mix2(state: [u8; 4], subkey: [u8; 4]) -> [u8; 4] {
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
      // take 4th and 0th bit
      let row = ((entry & 0b100000) >> 4) | (entry & 1);
      // take middle 4 bits
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
    let mixed = Self::mix(expanded, subkey);
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
      right = Self::mix2(left, Self::feistel_function(&right, self.subkeys[i]));
      left = temp;
    }

    let cipher: Block = [left, right]
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
      right = Self::mix2(left, Self::feistel_function(&right, self.subkeys[i]));
      left = temp;
    }

    let cipher: Block = [left, right]
      .concat()
      .try_into()
      .unwrap_or_else(|v: Vec<u8>| panic!("Expected vec of len: {} but got: {}", 8, v.len()));

    Self::final_permutation(&cipher)
  }
}
