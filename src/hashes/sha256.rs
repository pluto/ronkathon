use super::*;

/// The SHA-256 hash function uses random constants in the hash computation.
/// These constants here are the first 32 bits of the fractional parts of the cube roots of the
/// first 64 prime numbers.
const K: [u32; 64] = [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// The initial hash values for SHA-256.
/// These are the first 32 bits of the fractional parts of the square roots of the first 8 prime
/// numbers.
const H: [u32; 8] =
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];

/// A rotation function that rotates a 32-bit word to the right by `N` bits.
/// Note that the implementation here assumes that the bits are replaced by zeroes when shifted
/// hence the `|`.
pub const fn rot<const N: usize>(x: u32) -> u32 { (x >> N) | (x << (32 - N)) }

pub const fn cap_sigma_0(x: u32) -> u32 { rot::<2>(x) ^ rot::<13>(x) ^ rot::<22>(x) }

pub const fn cap_sigma_1(x: u32) -> u32 { rot::<6>(x) ^ rot::<11>(x) ^ rot::<25>(x) }

pub const fn small_sigma_0(x: u32) -> u32 { rot::<7>(x) ^ rot::<18>(x) ^ (x >> 3) }

pub const fn small_sigma_1(x: u32) -> u32 { rot::<17>(x) ^ rot::<19>(x) ^ (x >> 10) }

pub const fn ch(x: u32, y: u32, z: u32) -> u32 { (x & y) ^ (!x & z) }

pub const fn maj(x: u32, y: u32, z: u32) -> u32 { (x & y) ^ (x & z) ^ (y & z) }

pub struct Sha256;

impl Sha256 {
  pub fn digest(input: &[u8]) -> [u8; 32] {
    // Initialize the hash values.
    let mut hash = H;

    // Initialize the array of message words.
    let mut words = [0u32; 64];

    // Initialize the array of message bytes.
    let mut bytes = [0u8; 64];

    // Padding
    // The message is padded so that its length is congruent to 448 modulo 512.
    // We first get the length of the input in bits.
    let len = input.len() as u64 * 8;
    let len_with_1_appended = len + 1;
    let len_mod = len_with_1_appended % 512;
    let zero_padding = if len_mod > 448 { 512 + 448 - len_mod } else { 448 - len_mod };
    let len_padded = (len_with_1_appended as usize + zero_padding as usize) / 8;
    let len_bytes = (len).to_be_bytes();
    dbg!(len, len_mod, zero_padding);

    // Initialize the message with padding.
    let mut message = Vec::with_capacity(len_padded);
    message.extend_from_slice(input);
    message.push(0x80);
    message.extend(&vec![0; 56 - len as usize / 8 - 1]);
    message.extend_from_slice(&len_bytes);
    dbg!(message.len(), hex::encode(message.clone()));

    // Process the message in 512-bit blocks.
    for chunk in message.chunks(64) {
      // Copy the chunk into the bytes array.
      bytes.copy_from_slice(chunk);

      // Copy the bytes into the words array.
      for i in 0..16 {
        words[i] =
          u32::from_be_bytes([bytes[i * 4], bytes[i * 4 + 1], bytes[i * 4 + 2], bytes[i * 4 + 3]]);
      }

      // Use our permutations to complete the block decomposition
      for i in 16..64 {
        words[i] = small_sigma_1(words[i - 2])
          .wrapping_add(words[i - 7])
          .wrapping_add(small_sigma_0(words[i - 15]))
          .wrapping_add(words[i - 16]);
      }

      // Initialize the working variables.
      let mut a = hash[0];
      let mut b = hash[1];
      let mut c = hash[2];
      let mut d = hash[3];
      let mut e = hash[4];
      let mut f = hash[5];
      let mut g = hash[6];
      let mut h = hash[7];

      // Perform the main hash computation.
      for i in 0..64 {
        let temp1 = h
          .wrapping_add(cap_sigma_1(e))
          .wrapping_add(ch(e, f, g))
          .wrapping_add(K[i])
          .wrapping_add(words[i]);
        let temp2 = cap_sigma_0(a).wrapping_add(maj(a, b, c));

        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(temp1);
        d = c;
        c = b;
        b = a;
        a = temp1.wrapping_add(temp2);
      }

      // Update the hash values.
      hash[0] = hash[0].wrapping_add(a);
      hash[1] = hash[1].wrapping_add(b);
      hash[2] = hash[2].wrapping_add(c);
      hash[3] = hash[3].wrapping_add(d);
      hash[4] = hash[4].wrapping_add(e);
      hash[5] = hash[5].wrapping_add(f);
      hash[6] = hash[6].wrapping_add(g);
      hash[7] = hash[7].wrapping_add(h);
    }

    for i in 0..8 {
      hash[i] = hash[i].to_be();
    }

    unsafe { std::mem::transmute(hash) }
  }
}

#[cfg(test)]
mod tests {

  use super::*;
  #[test]
  fn sha256_hash() {
    let input = b"abc";
    let output = Sha256::digest(input);
    assert_eq!(
      hex::encode(output),
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
  }
}
