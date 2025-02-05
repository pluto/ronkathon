//! This module implements the SHA-3 and SHAKE algorithms using the Keccak permutation.
//! It provides generic implementations of SHA3 and Shake, parameterized by the digest size
//! or security bits respectively. The implementation follows the multi-rate padding scheme
//! specified in FIPS-202.

const KECCAK_ROUNDS: usize = 24;
const DELIM_SHA3: u8 = 0x06;
const DELIM_SHAKE: u8 = 0x1F;

/// Round constants for Keccak-f[1600]
const RC: [u64; 24] = [
  0x0000000000000001,
  0x0000000000008082,
  0x800000000000808A,
  0x8000000080008000,
  0x000000000000808B,
  0x0000000080000001,
  0x8000000080008081,
  0x8000000000008009,
  0x000000000000008A,
  0x0000000000000088,
  0x0000000080008009,
  0x000000008000000A,
  0x000000008000808B,
  0x800000000000008B,
  0x8000000000008089,
  0x8000000000008003,
  0x8000000000008002,
  0x8000000000000080,
  0x000000000000800A,
  0x800000008000000A,
  0x8000000080008081,
  0x8000000000008080,
  0x0000000080000001,
  0x8000000080008008,
];

/// Rotation offsets for ρ step
const RHO: [[u32; 5]; 5] =
  [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56], [
    27, 20, 39, 8, 14,
  ]];

#[derive(Clone, Debug)]
struct KeccakState {
  lanes: [[u64; 5]; 5],
}

impl KeccakState {
  fn new() -> Self { Self { lanes: [[0; 5]; 5] } }

  fn keccak_f1600(&mut self) {
    for round in 0..KECCAK_ROUNDS {
      // θ step
      let mut c = [0u64; 5];
      for x in 0..5 {
        c[x] = self.lanes[x][0]
          ^ self.lanes[x][1]
          ^ self.lanes[x][2]
          ^ self.lanes[x][3]
          ^ self.lanes[x][4];
      }

      let mut d = [0u64; 5];
      for x in 0..5 {
        d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
      }

      for x in 0..5 {
        for y in 0..5 {
          self.lanes[x][y] ^= d[x];
        }
      }

      // ρ and π steps
      let mut b = [[0u64; 5]; 5];
      let mut x = 1;
      let mut y = 0;
      let mut current = self.lanes[x][y];

      for t in 0..24 {
        let new_x = y;
        let new_y = (2 * x + 3 * y) % 5;
        let rot = ((t + 1) * (t + 2) / 2) % 64;
        b[new_x][new_y] = current.rotate_left(rot as u32);
        x = new_x;
        y = new_y;
        current = self.lanes[x][y];
      }
      b[0][0] = self.lanes[0][0];

      // χ step
      for x in 0..5 {
        for y in 0..5 {
          self.lanes[x][y] = b[x][y] ^ ((!b[(x + 1) % 5][y]) & b[(x + 2) % 5][y]);
        }
      }

      // ι step
      self.lanes[0][0] ^= RC[round];
    }
  }

  fn absorb(&mut self, input: &[u8], rate: usize) {
    debug_assert!(rate % 8 == 0, "Rate must be multiple of 8 bits");
    let rate_bytes = rate / 8;

    for chunk in input.chunks(rate_bytes) {
      // Convert bytes to lanes
      for i in (0..chunk.len()).step_by(8) {
        let x = (i / 8) % 5;
        let y = (i / 8) / 5;
        if x < 5 && y < 5 {
          let mut lane = 0u64;
          for j in 0..8 {
            if i + j < chunk.len() {
              lane |= (chunk[i + j] as u64) << (j * 8);
            }
          }
          self.lanes[x][y] ^= lane;
        }
      }
      self.keccak_f1600();
    }
  }

  fn squeeze(&mut self, output: &mut [u8], rate: usize) {
    debug_assert!(rate % 8 == 0, "Rate must be multiple of 8 bits");
    let rate_bytes = rate / 8;

    let mut offset = 0;
    while offset < output.len() {
      let bytes_to_squeeze = std::cmp::min(rate_bytes, output.len() - offset);
      for i in 0..bytes_to_squeeze {
        let x = (i / 8) % 5;
        let y = (i / 8) / 5;
        let shift = (i % 8) * 8;
        output[offset + i] = ((self.lanes[x][y] >> shift) & 0xFF) as u8;
      }
      offset += bytes_to_squeeze;
      if offset < output.len() {
        self.keccak_f1600();
      }
    }
  }
}

/// A generic implementation of the SHA-3 hash function.
///
/// The generic parameter `DIGEST_BYTES` specifies the size (in bytes) of the final digest.
pub struct Sha3<const DIGEST_BYTES: usize> {
  state:  KeccakState,
  buffer: Vec<u8>,
  rate:   usize,
}

impl<const DIGEST_BYTES: usize> Sha3<DIGEST_BYTES> {
  /// Creates a new instance of a SHA-3 hasher.
  ///
  /// The capacity is calculated as `DIGEST_BYTES * 8 * 2`, and the rate is set to
  /// `1600 - capacity`.
  pub fn new() -> Self {
    let capacity = DIGEST_BYTES * 8 * 2;
    let rate = 1600 - capacity;
    Self { state: KeccakState::new(), buffer: Vec::new(), rate }
  }

  /// Absorbs input data into the hash state.
  ///
  /// Data is buffered until enough bytes (a full block) have been accumulated.
  /// Full blocks are then absorbed into the state using the Keccak absorption routine.
  pub fn update(&mut self, input: &[u8]) {
    self.buffer.extend_from_slice(input);
    let rate_bytes = self.rate / 8;

    while self.buffer.len() >= rate_bytes {
      self.state.absorb(&self.buffer[..rate_bytes], self.rate);
      self.buffer.drain(..rate_bytes);
    }
  }

  /// Finalizes the hashing process and returns the computed digest.
  ///
  /// This method appends the SHA3-specific domain separator followed by padding according
  /// to the multi-rate padding rules, then performs a final absorption of the padded block.
  /// Finally, it squeezes the state to produce the output digest.
  ///
  /// # Panics
  ///
  /// This function panics if the final padded block cannot be produced.
  pub fn finalize(mut self) -> [u8; DIGEST_BYTES] {
    // Append the domain separator for SHA3.
    self.buffer.push(DELIM_SHA3);
    let rate_bytes = self.rate / 8;
    // Pad with zeros until a full block is reached.
    while self.buffer.len() < rate_bytes {
      self.buffer.push(0);
    }
    // Set the most-significant bit (final bit) in the last byte.
    *self.buffer.last_mut().unwrap() |= 0x80;

    // Absorb the final padded block.
    self.state.absorb(&self.buffer, self.rate);

    let mut output = [0u8; DIGEST_BYTES];
    self.state.squeeze(&mut output, self.rate);
    output
  }
}

/// A generic implementation of the SHAKE extendable output function (XOF).
///
/// The generic parameter `SECURITY_BITS` specifies the level of security (in bits)
/// and influences the capacity and rate.
pub struct Shake<const SECURITY_BITS: usize> {
  state:     KeccakState,
  buffer:    Vec<u8>,
  rate:      usize,
  finalized: bool,
}

impl<const SECURITY_BITS: usize> Shake<SECURITY_BITS> {
  /// Creates a new instance of a SHAKE hasher.
  ///
  /// The capacity is calculated as `SECURITY_BITS * 2`, with the rate set to
  /// `1600 - capacity`.
  pub fn new() -> Self {
    let capacity = SECURITY_BITS * 2;
    let rate = 1600 - capacity;
    Self { state: KeccakState::new(), buffer: Vec::new(), rate, finalized: false }
  }

  /// Absorbs input data into the SHAKE state.
  ///
  /// Data is buffered until a full block is available, and then absorbed using the
  /// Keccak absorption routine.
  ///
  /// # Panics
  ///
  /// Panics if called after the first `squeeze` operation.
  pub fn update(&mut self, input: &[u8]) {
    assert!(!self.finalized, "Cannot update after squeezing");
    self.buffer.extend_from_slice(input);
    let rate_bytes = self.rate / 8;

    while self.buffer.len() >= rate_bytes {
      self.state.absorb(&self.buffer[..rate_bytes], self.rate);
      self.buffer.drain(..rate_bytes);
    }
  }

  /// Finalizes the absorption phase if not already performed.
  ///
  /// This method appends the SHAKE-specific domain separator and appropriate padding,
  /// then absorbs the final block into the state.
  fn finalize_if_needed(&mut self) {
    if !self.finalized {
      self.buffer.push(DELIM_SHAKE);
      let rate_bytes = self.rate / 8;
      while self.buffer.len() < rate_bytes {
        self.buffer.push(0);
      }
      *self.buffer.last_mut().unwrap() |= 0x80;

      self.state.absorb(&self.buffer, self.rate);
      self.buffer.clear();
      self.finalized = true;
    }
  }

  /// Squeezes the desired amount of output from the SHAKE state.
  ///
  /// If needed, the final padded block is absorbed before squeezing begins.
  pub fn squeeze(&mut self, output: &mut [u8]) {
    self.finalize_if_needed();
    self.state.squeeze(output, self.rate);
  }
}

/// Type alias for SHA3-224.
pub type Sha3_224 = Sha3<28>;
/// Type alias for SHA3-256.
pub type Sha3_256 = Sha3<32>;
/// Type alias for SHA3-384.
pub type Sha3_384 = Sha3<48>;
/// Type alias for SHA3-512.
pub type Sha3_512 = Sha3<64>;
/// Type alias for SHAKE128.
pub type Shake128 = Shake<128>;
/// Type alias for SHAKE256.
pub type Shake256 = Shake<256>;

#[cfg(test)]
mod tests {
  use hex_literal::hex;

  use super::*;

  /// Tests SHA3-224 against known test vectors.
  #[test]
  fn test_sha3_224() {
    let mut hasher = Sha3_224::new();
    hasher.update(b"");
    assert_eq!(
      hasher.finalize()[..],
      hex!("6b4e03423667dbb73b6e15454f0eb1abd4597f9a1b078e3f5b5a6bc7")[..]
    );

    let mut hasher = Sha3_224::new();
    hasher.update(b"abc");
    assert_eq!(
      hasher.finalize()[..],
      hex!("e642824c3f8cf24ad09234ee7d3c766fc9a3a5168d0c94ad73b46fdf")[..]
    );
  }

  /// Tests SHA3-256 against known test vectors.
  #[test]
  fn test_sha3_256() {
    let mut hasher = Sha3_256::new();
    hasher.update(b"");
    assert_eq!(
      hasher.finalize()[..],
      hex!("a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a")[..]
    );

    let mut hasher = Sha3_256::new();
    hasher.update(b"abc");
    assert_eq!(
      hasher.finalize()[..],
      hex!("3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532")[..]
    );
  }

  /// Tests SHAKE128 output against known test vectors.
  #[test]
  fn test_shake128() {
    let mut hasher = Shake128::new();
    hasher.update(b"abc");
    let mut output = [0u8; 32];
    hasher.squeeze(&mut output);
    assert_eq!(
      output[..],
      hex!("5881092dd818bf5cf8a3ddb793fbcba74097d5c526a6d35f97b83351940f2cc8")[..]
    );
  }

  /// Tests SHAKE256 output against known test vectors.
  #[test]
  fn test_shake256() {
    let mut hasher = Shake256::new();
    hasher.update(b"abc");
    let mut output = [0u8; 64];
    hasher.squeeze(&mut output);
    assert_eq!(
            output[..],
            hex!("483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739d5a15bef186a5386c75744c0527e1faa9f8726e462a12a4feb06bd8801e751e4")[..]
        );
  }
}
