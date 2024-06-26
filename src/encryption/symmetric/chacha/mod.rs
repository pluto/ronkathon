//! Contains implemenation of ChaCha stream cipher algorithm.

use itertools::Itertools;
#[cfg(test)] mod tests;

pub const STATE_WORDS: usize = 16;

pub type ChaCha20 = ChaCha<20>;
pub type ChaCha12 = ChaCha<12>;
pub type ChaCha8 = ChaCha<8>;

pub struct ChaCha<const R: usize> {
  rounds: usize,
}

/// Nothing-up-my-sleeve constant: `["expa", "nd 3", "2-by", "te-k"]`
pub const CONSTS: [u32; 4] = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574];

impl<const R: usize> ChaCha<R> {
  pub fn new(rounds: usize) -> Self { Self { rounds } }

  pub fn encrypt(
    &self,
    key: [u32; 8],
    counter: [u32; 1],
    nonce: [u32; 3],
    plaintext: &[u8],
  ) -> Vec<u8> {
    debug_assert_eq!(counter.len() + nonce.len(), 4);

    let mut encrypted: Vec<u8> = Vec::new();

    let chunks = plaintext.chunks_exact(64);
    let remainder = chunks.remainder();

    for (i, chunk) in chunks.enumerate() {
      let keystream = block(key, [counter[0] + i as u32], nonce, self.rounds);
      let res: Vec<u8> = keystream.iter().zip(chunk).map(|(a, b)| a ^ b).collect();
      encrypted.extend(res);
    }

    if !remainder.is_empty() {
      let size = plaintext.len() / 64;
      let keystream = block(key, [counter[0] + size as u32], nonce, self.rounds);
      let res: Vec<u8> = remainder.iter().zip(keystream).map(|(a, b)| a ^ b).collect();
      encrypted.extend(res);
    }

    encrypted
  }

  pub fn decrypt(
    &self,
    key: [u32; 8],
    counter: [u32; 1],
    nonce: [u32; 3],
    ciphertext: &[u8],
  ) -> Vec<u8> {
    Self::encrypt(&self, key, counter, nonce, ciphertext)
  }
}

fn block(key: [u32; 8], counter: [u32; 1], nonce: [u32; 3], rounds: usize) -> [u8; 64] {
  let mut state: Vec<u32> = CONSTS.to_vec();
  state.extend_from_slice(&key);
  state.extend_from_slice(&counter);
  state.extend_from_slice(&nonce);

  let mut initial_state: [u32; 16] = state
    .clone()
    .try_into()
    .unwrap_or_else(|v: Vec<u32>| panic!("expected vec of len: {} but got: {}", 16, v.len()));

  for _ in 0..rounds / 2 {
    column_rounds(&mut initial_state);
    diagonal_rounds(&mut initial_state);
  }

  let state: [u32; 16] = state
    .into_iter()
    .zip(initial_state)
    .map(|(a, b)| a.wrapping_add(b))
    .collect::<Vec<u32>>()
    .try_into()
    .unwrap_or_else(|v: Vec<u32>| panic!("expected vec of len: {} but got: {}", 16, v.len()));

  let mut output = [0u8; 64];
  state.iter().flat_map(|v| v.to_le_bytes()).enumerate().for_each(|(i, byte)| output[i] = byte);

  output
}

const fn column_rounds(state: &mut [u32; STATE_WORDS]) {
  quarter_round(0, 4, 8, 12, state);
  quarter_round(1, 5, 9, 13, state);
  quarter_round(2, 6, 10, 14, state);
  quarter_round(3, 7, 11, 15, state);
}

const fn diagonal_rounds(state: &mut [u32; STATE_WORDS]) {
  quarter_round(0, 5, 10, 15, state);
  quarter_round(1, 6, 11, 12, state);
  quarter_round(2, 7, 8, 13, state);
  quarter_round(3, 4, 9, 14, state);
}

const fn quarter_round(a: usize, b: usize, c: usize, d: usize, state: &mut [u32; STATE_WORDS]) {
  state[a] = state[a].wrapping_add(state[b]);
  state[d] ^= state[a];
  state[d] = state[d].rotate_left(16);

  state[c] = state[c].wrapping_add(state[d]);
  state[b] ^= state[c];
  state[b] = state[b].rotate_left(12);

  state[a] = state[a].wrapping_add(state[b]);
  state[d] ^= state[a];
  state[d] = state[d].rotate_left(8);

  state[c] = state[c].wrapping_add(state[d]);
  state[b] ^= state[c];
  state[b] = state[b].rotate_left(7);
}
