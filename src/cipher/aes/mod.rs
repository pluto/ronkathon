use itertools::Itertools;

use crate::cipher::{Block, BlockCipher, Key, Word};

/// https://en.wikipedia.org/wiki/AES_key_schedule#Round_constants
const ROUND_CONSTANTS: [[u8; 4]; 10] = [
  [0x01, 0x00, 0x00, 0x00],
  [0x02, 0x00, 0x00, 0x00],
  [0x04, 0x00, 0x00, 0x00],
  [0x08, 0x00, 0x00, 0x00],
  [0x10, 0x00, 0x00, 0x00],
  [0x20, 0x00, 0x00, 0x00],
  [0x40, 0x00, 0x00, 0x00],
  [0x80, 0x00, 0x00, 0x00],
  [0x1B, 0x00, 0x00, 0x00],
  [0x36, 0x00, 0x00, 0x00],
];

#[derive(Clone)]
pub struct AES<const K: usize, const B: usize>
where [(); K / 8]: {
  key:          Key<K>,
  expanded_key: Vec<Word>,
  state:        State,
  num_rounds:   usize,
  sbox:         SBox,
}

/// Instead of arranging its bytes in a line (array),
/// AES operates on a grid, specifically a 4x4 column-major array:
///
/// [[b_0, b_4, b_8,  b_12],
///  [b_1, b_5, b_9,  b_13],
///  [b_2, b_6, b_10, b_14],
///  [b_3, b_7, b_11, b_15]]
///
/// where b_i is the i-th byte. This is also how we will layout
/// bytes in our `State`.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
struct State([[u8; 4]; 4]);

impl From<[u8; 16]> for State {
  fn from(plaintext: [u8; 16]) -> Self {
    Self(
      plaintext
        .chunks(4)
        .map(|c| c.try_into().unwrap())
        .collect::<Vec<[u8; 4]>>()
        .try_into()
        .unwrap(),
    )
  }
}

impl BlockCipher<128, 128> for AES<128, 128> {
  /// Encryption
  fn encrypt(&mut self, key: Key<128>, plaintext: [u8; 16]) -> Block<128> {
    self.key = key;
    assert!(self.key.inner != [0; 16], "Key is not instantiated");

    let out_len = Self::KEY_LEN_WORDS * (self.num_rounds + 1);
    self.expanded_key = Vec::with_capacity(out_len);
    self.key_expansion(Self::KEY_LEN_WORDS);

    self.state = State::from(plaintext);
    assert!(self.state != State::default(), "State is not instantiated");

    // Round 0 - add round key
    self.add_round_key(0);

    // Rounds 1 to N - 1
    for i in 1..self.num_rounds {
      self.sub_bytes();
      self.shift_rows();
      self.mix_columns();
      self.add_round_key(i);
    }

    // Last round - we do not mix columns here.
    self.sub_bytes();
    self.shift_rows();
    self.add_round_key(self.num_rounds);

    Block([0; 128])
  }

  fn decrypt(self, _key: Key<128>, _ciphertext: Block<128>) -> Block<128> { unimplemented!() }
}

impl BlockCipher<128, 192> for AES<192, 128> {
  /// Encryption
  fn encrypt(&mut self, key: Key<192>, plaintext: [u8; 16]) -> Block<128> {
    self.key = key;
    assert!(self.key.inner != [0; 24], "Key is not instantiated");

    let out_len = Self::KEY_LEN_WORDS * (self.num_rounds + 1);
    self.expanded_key = Vec::with_capacity(out_len);
    self.key_expansion(Self::KEY_LEN_WORDS);

    self.state = State::from(plaintext);
    assert!(self.state != State::default(), "State is not instantiated");

    // Round 0 - add round key
    self.add_round_key(0);

    // Rounds 1 to N - 1
    for i in 1..self.num_rounds {
      self.sub_bytes();
      self.shift_rows();
      self.mix_columns();
      self.add_round_key(i);
    }

    // Last round - we do not mix columns here.
    self.sub_bytes();
    self.shift_rows();
    self.add_round_key(self.num_rounds);

    Block([0; 128])
  }

  fn decrypt(self, _key: Key<192>, _ciphertext: Block<128>) -> Block<128> { unimplemented!() }
}

impl BlockCipher<128, 256> for AES<256, 128> {
  /// Encryption
  fn encrypt(&mut self, key: Key<256>, plaintext: [u8; 16]) -> Block<128> {
    self.key = key;
    assert!(self.key.inner != [0; 32], "Key is not instantiated");

    let out_len = Self::KEY_LEN_WORDS * (self.num_rounds + 1);
    self.expanded_key = Vec::with_capacity(out_len);
    self.key_expansion(Self::KEY_LEN_WORDS);

    self.state = State::from(plaintext);
    assert!(self.state != State::default(), "State is not instantiated");

    // Round 0 - add round key
    self.add_round_key(0);

    // Rounds 1 to N - 1
    for i in 1..self.num_rounds {
      self.sub_bytes();
      self.shift_rows();
      self.mix_columns();
      self.add_round_key(i);
    }

    // Last round - we do not mix columns here.
    self.sub_bytes();
    self.shift_rows();
    self.add_round_key(self.num_rounds);

    Block([0; 128])
  }

  fn decrypt(self, _key: Key<256>, _ciphertext: Block<128>) -> Block<128> { unimplemented!() }
}

/// A Rijndael S-box.
///
/// TODO(bing): Consider deriving these substitution boxes perhaps?
#[derive(Copy, Clone)]
pub struct SBox([u8; 256]);

impl SBox {
  /// # Filling the entries of the SBox
  ///
  /// The high level description is as follows:
  /// 1. Invert in GF(2^8),
  /// 2. Multiply by a matrix `L`,
  /// 3. Add a constant `c`.
  ///
  /// For convenience, we use the calculated version.
  ///
  /// Source: https://www.johndcook.com/blog/2019/05/25/aes-s-box/
  pub fn new() -> Self {
    Self([
      0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab,
      0x76, 0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4,
      0x72, 0xc0, 0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71,
      0xd8, 0x31, 0x15, 0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2,
      0xeb, 0x27, 0xb2, 0x75, 0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6,
      0xb3, 0x29, 0xe3, 0x2f, 0x84, 0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb,
      0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf, 0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45,
      0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8, 0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5,
      0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2, 0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44,
      0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73, 0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a,
      0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb, 0xe0, 0x32, 0x3a, 0x0a, 0x49,
      0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79, 0xe7, 0xc8, 0x37, 0x6d,
      0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08, 0xba, 0x78, 0x25,
      0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a, 0x70, 0x3e,
      0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e, 0xe1,
      0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
      0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb,
      0x16,
    ])
  }
}

impl<const K: usize, const B: usize> AES<K, B>
where [(); K / 8]:
{
  /// Instantiates a new `AES` instance according to `key_size` - this
  /// affects the number of rounds that the AES encryption will do.
  fn new() -> Self {
    let num_rounds = match K {
      128 => 10,
      192 => 12,
      256 => 14,
      _ => unimplemented!(),
    };

    Self {
      num_rounds,
      key: Key { inner: [0; K / 8] },
      expanded_key: Vec::new(),
      state: State::default(),
      sbox: SBox::new(),
    }
  }

  /// XOR a round key to its internal state.
  fn add_round_key(&mut self, round_num: usize) {
    let words = &self.expanded_key[round_num * 4..(round_num + 1) * 4];
    for (col, word) in self.state.0.iter_mut().zip(words.iter()) {
      for (c, w) in col.iter_mut().zip(word.iter()) {
        *c ^= w;
      }
    }
  }

  /// Substitutes each byte [s_0, s_1, ..., s_15] with another byte according to a substitution box
  /// (usually referred to as an S-box).
  fn sub_bytes(&mut self) {
    for i in 0..4 {
      for j in 0..4 {
        self.state.0[i][j] = self.sbox.0[self.state.0[i][j] as usize];
      }
    }
  }

  /// Shift i-th row of i positions, for i ranging from 0 to 3.
  ///
  /// For row 0, no shifting occurs, for row 1, a left shift of 1 index occurs, ..
  ///
  /// Note that since our state is in column-major form, we transpose the state to a
  /// row-major form to make this step simpler.
  fn shift_rows(&mut self) {
    let len = self.state.0.len();
    let mut iters: Vec<_> = self.state.0.into_iter().map(|n| n.into_iter()).collect();

    // Transpose to row-major form
    let mut transposed: Vec<_> =
      (0..len).map(|_| iters.iter_mut().map(|n| n.next().unwrap()).collect::<Vec<_>>()).collect();

    for (r, i) in transposed.iter_mut().zip(0..4) {
      let (left, right) = r.split_at(i);
      *r = [right.to_vec(), left.to_vec()].concat();
    }
    let mut iters: Vec<_> = transposed.into_iter().map(|n| n.into_iter()).collect();

    let new_state = (0..len)
      .map(|_| iters.iter_mut().map(|n| n.next().unwrap()).collect::<Vec<_>>().try_into().unwrap())
      .collect::<Vec<_>>()
      .try_into()
      .unwrap();
    self.state.0 = new_state;
  }

  /// Applies the same linear transformation to each of the four columns of the state.
  ///
  /// Mix columns is done as such:
  ///
  /// Each column of bytes is treated as a 4-term polynomial, multiplied by a fixed polynomial
  /// a(x) = 3x^3 + x^2 + x + 2.
  fn mix_columns(&mut self) {
    for col in self.state.0.iter_mut() {
      let tmp = col.clone();
      let mut col_doubled = col.clone();

      for (i, c) in col_doubled.iter_mut().enumerate() {
        let hi_bit = col[i] >> 7;
        *c = col[i] << 1;
        *c ^= hi_bit * 0x1B;
      }

      col[0] = col_doubled[0] ^ tmp[3] ^ tmp[2] ^ col_doubled[1] ^ tmp[1];
      col[1] = col_doubled[1] ^ tmp[0] ^ tmp[3] ^ col_doubled[2] ^ tmp[2];
      col[2] = col_doubled[2] ^ tmp[1] ^ tmp[0] ^ col_doubled[3] ^ tmp[3];
      col[3] = col_doubled[3] ^ tmp[2] ^ tmp[1] ^ col_doubled[0] ^ tmp[0];
    }
  }

  /// In AES, rotword() is just a one-byte left circular shift.
  fn rotate_word(&self, word: &mut [u8; 4]) { word.rotate_left(1) }

  /// In AES, subword() is just an application of the S-box to each of the
  /// four bytes of a word.
  fn sub_word(&self, mut word: [u8; 4]) -> [u8; 4] {
    word.iter_mut().for_each(|b| *b = self.sbox.0[*b as usize]);

    word
  }

  fn key_expansion(&mut self, key_len: usize) {
    let block_num_words = 128 / 32;

    let out_len = block_num_words * (self.num_rounds + 1);

    let key_words: Vec<_> = self
      .key
      .inner
      .chunks(4)
      .map(|c| c.try_into().unwrap())
      .collect::<Vec<[u8; 4]>>()
      .try_into()
      .unwrap();

    self.expanded_key.extend(key_words);

    // key len (Nk words)
    // block size (Nb words)
    // num rounds (Nr)
    for i in key_len..(block_num_words * (self.num_rounds + 1)) {
      let mut last = self.expanded_key.last().unwrap().clone();

      if i % key_len == 0 {
        self.rotate_word(&mut last);
        last = (u32::from_le_bytes(self.sub_word(last))
          ^ u32::from_le_bytes(ROUND_CONSTANTS[(i / key_len) - 1]))
        .to_le_bytes();
      } else if key_len > 6 && i % key_len == 4 {
        last = self.sub_word(last)
      }

      self.expanded_key.push(
        self.expanded_key[i - key_len]
          .iter()
          .zip(last.iter())
          .map(|(w, l)| w ^ l)
          .collect_vec()
          .try_into()
          .unwrap(),
      );
    }

    assert_eq!(
      self.expanded_key.len(),
      out_len,
      "Wrong number of words output during key expansion"
    );
  }
}

#[cfg(test)]
mod tests {
  use pretty_assertions::assert_eq;

  use super::{BlockCipher, *};

  #[test]
  // Test vector from: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197.pdf
  fn test_aes_128() {
    const KEY_LEN: usize = 128;
    const BLOCK_LEN: usize = 128;
    let key = Key::<KEY_LEN>::new([
      0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
      0x0f,
    ]);

    let plaintext = [
      0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
      0xff,
    ];

    let mut aes = AES::<KEY_LEN, BLOCK_LEN>::new();
    aes.encrypt(key, plaintext);

    let expected_state = State::from([
      0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5,
      0x5a,
    ]);

    assert_eq!(aes.state, expected_state);
  }

  #[test]
  // Test vector from: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197.pdf
  fn test_aes_192() {
    const KEY_LEN: usize = 192;
    const BLOCK_LEN: usize = 128;
    let key = Key::<KEY_LEN>::new([
      0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
      0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    ]);

    let plaintext = [
      0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
      0xff,
    ];

    let mut aes = AES::<KEY_LEN, BLOCK_LEN>::new();
    aes.encrypt(key, plaintext);

    let expected_state = State::from([
      0xdd, 0xa9, 0x7c, 0xa4, 0x86, 0x4c, 0xdf, 0xe0, 0x6e, 0xaf, 0x70, 0xa0, 0xec, 0x0d, 0x71,
      0x91,
    ]);

    assert_eq!(aes.state, expected_state);
  }

  #[test]
  // Test vector from: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197.pdf
  fn test_aes_256() {
    const KEY_LEN: usize = 256;
    const BLOCK_LEN: usize = 128;
    let key = Key::<KEY_LEN>::new([
      0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
      0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d,
      0x1e, 0x1f,
    ]);

    let plaintext = [
      0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
      0xff,
    ];

    let mut aes = AES::<KEY_LEN, BLOCK_LEN>::new();
    aes.encrypt(key, plaintext);

    let expected_state = State::from([
      0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf, 0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49, 0x60,
      0x89,
    ]);

    assert_eq!(aes.state, expected_state);
  }

  #[test]
  /// Test vectors from:
  /// https://en.wikipedia.org/wiki/Rijndael_MixColumns#Test_vectors_for_MixColumn()
  fn test_mix_columns() {
    const KEY_LEN: usize = 128;
    const BLOCK_LEN: usize = 128;

    {
      let key = Key::<128>::new([0; 16]);
      let input = [219, 19, 83, 69, 242, 10, 34, 92, 1, 1, 1, 1, 198, 198, 198, 198];
      let expected_state =
        State::from([142, 77, 161, 188, 159, 220, 88, 157, 1, 1, 1, 1, 198, 198, 198, 198]);

      let mut aes = AES::<KEY_LEN, BLOCK_LEN>::new();
      aes.key = key;
      aes.state = State::from(input);

      aes.mix_columns();
      assert_eq!(aes.state, expected_state);
    }

    {
      let key = Key::<KEY_LEN>::new([0; 16]);
      let input = [212, 212, 212, 213, 45, 38, 49, 76, 1, 1, 1, 1, 198, 198, 198, 198];
      let expected_state =
        State::from([213, 213, 215, 214, 77, 126, 189, 248, 1, 1, 1, 1, 198, 198, 198, 198]);

      let mut aes = AES::<KEY_LEN, BLOCK_LEN>::new();
      aes.key = key;
      aes.state = State::from(input);

      aes.mix_columns();
      assert_eq!(aes.state, expected_state);
    }
  }
}
