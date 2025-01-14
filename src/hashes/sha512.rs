//! Implementation of SHA-512 hash function.
//! References:
//! [SHS]: "Secure Hash Standard", National Institute of Science and Technology, Federal Information Processing Standard (FIPS) 180-3, https://csrc.nist.gov/files/pubs/fips/180-3/final/docs/fips180-3_final.pdf.

/// A rotation function that rotates a 64-bit word to the right by `N` bits.
/// Note that the implementation here assumes that the bits are replaced by zeroes when shifted
/// hence the `|`.
pub const fn rotate_right<const N: usize>(x: u64) -> u64 { (x >> N) | (x << (64 - N)) }

/// The [Σ0](https://csrc.nist.gov/files/pubs/fips/180-3/final/docs/fips180-3_final.pdf) function used in SHA-512.
/// This is one of the compression functions used in the hash computation.
pub const fn sigma_0(x: u64) -> u64 {
  rotate_right::<28>(x) ^ rotate_right::<34>(x) ^ rotate_right::<39>(x)
}

/// The [Σ1](https://csrc.nist.gov/files/pubs/fips/180-3/final/docs/fips180-3_final.pdf) function used in SHA-512.
/// This is one of the compression functions used in the hash computation.
pub const fn sigma_1(x: u64) -> u64 {
  rotate_right::<14>(x) ^ rotate_right::<18>(x) ^ rotate_right::<41>(x)
}

/// The [σ0](https://csrc.nist.gov/files/pubs/fips/180-3/final/docs/fips180-3_final.pdf) function used in SHA-512.
/// This is one of the message schedule functions used in the hash computation.
pub const fn small_sigma_0(x: u64) -> u64 { rotate_right::<1>(x) ^ rotate_right::<8>(x) ^ (x >> 7) }

/// The [σ1](https://csrc.nist.gov/files/pubs/fips/180-3/final/docs/fips180-3_final.pdf) function
/// used in SHA-512
/// This is one of the message schedule functions used in the hash computation.
pub const fn small_sigma_1(x: u64) -> u64 {
  rotate_right::<19>(x) ^ rotate_right::<61>(x) ^ (x >> 6)
}

/// The [Ch](https://csrc.nist.gov/files/pubs/fips/180-3/final/docs/fips180-3_final.pdf) function used in SHA-512.
/// This is a logical function used in the hash computation used to "choose" between `y` and `z`
/// given `x` as a conditional.
pub const fn ch(x: u64, y: u64, z: u64) -> u64 { (x & y) ^ (!x & z) }

/// The [Maj](https://csrc.nist.gov/files/pubs/fips/180-3/final/docs/fips180-3_final.pdf) function used in SHA-512.
/// This is a logical function used in the hash computation used to select the "majority" of the
/// values of `x`, `y`, and `z`.
pub const fn maj(x: u64, y: u64, z: u64) -> u64 { (x & y) ^ (x & z) ^ (y & z) }

const K: [u64; 80] = [
  0x428a2f98d728ae22,
  0x7137449123ef65cd,
  0xb5c0fbcfec4d3b2f,
  0xe9b5dba58189dbbc,
  0x3956c25bf348b538,
  0x59f111f1b605d019,
  0x923f82a4af194f9b,
  0xab1c5ed5da6d8118,
  0xd807aa98a3030242,
  0x12835b0145706fbe,
  0x243185be4ee4b28c,
  0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f,
  0x80deb1fe3b1696b1,
  0x9bdc06a725c71235,
  0xc19bf174cf692694,
  0xe49b69c19ef14ad2,
  0xefbe4786384f25e3,
  0x0fc19dc68b8cd5b5,
  0x240ca1cc77ac9c65,
  0x2de92c6f592b0275,
  0x4a7484aa6ea6e483,
  0x5cb0a9dcbd41fbd4,
  0x76f988da831153b5,
  0x983e5152ee66dfab,
  0xa831c66d2db43210,
  0xb00327c898fb213f,
  0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2,
  0xd5a79147930aa725,
  0x06ca6351e003826f,
  0x142929670a0e6e70,
  0x27b70a8546d22ffc,
  0x2e1b21385c26c926,
  0x4d2c6dfc5ac42aed,
  0x53380d139d95b3df,
  0x650a73548baf63de,
  0x766a0abb3c77b2a8,
  0x81c2c92e47edaee6,
  0x92722c851482353b,
  0xa2bfe8a14cf10364,
  0xa81a664bbc423001,
  0xc24b8b70d0f89791,
  0xc76c51a30654be30,
  0xd192e819d6ef5218,
  0xd69906245565a910,
  0xf40e35855771202a,
  0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8,
  0x1e376c085141ab53,
  0x2748774cdf8eeb99,
  0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63,
  0x4ed8aa4ae3418acb,
  0x5b9cca4f7763e373,
  0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc,
  0x78a5636f43172f60,
  0x84c87814a1f0ab72,
  0x8cc702081a6439ec,
  0x90befffa23631e28,
  0xa4506cebde82bde9,
  0xbef9a3f7b2c67915,
  0xc67178f2e372532b,
  0xca273eceea26619c,
  0xd186b8c721c0c207,
  0xeada7dd6cde0eb1e,
  0xf57d4f7fee6ed178,
  0x06f067aa72176fba,
  0x0a637dc5a2c898a6,
  0x113f9804bef90dae,
  0x1b710b35131c471b,
  0x28db77f523047d84,
  0x32caab7b40c72493,
  0x3c9ebe0a15c9bebc,
  0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6,
  0x597f299cfc657e2a,
  0x5fcb6fab3ad6faec,
  0x6c44198c4a475817,
];

const H: [u64; 8] = [
  0x6A09E667F3BCC908,
  0xBB67AE8584CAA73B,
  0x3C6EF372FE94F82B,
  0xA54FF53A5F1D36F1,
  0x510E527FADE682D1,
  0x9B05688C2B3E6C1F,
  0x1F83D9ABFB41BD6B,
  0x5BE0CD19137E2179,
];
/// Struct encapsulating SHA-512 hash function.
pub struct Sha512;

impl Sha512 {
  /// The SHA-512 hash function.
  /// This function takes an input byte array and returns a 64-byte array representing the hash
  /// of the input.
  ///
  /// # Arguments
  /// * `input` - A byte array representing the input to the hash function.
  ///
  /// # Returns
  /// A 64-byte array representing the hash of the input.
  ///
  /// # Example
  /// ```
  /// use hex;
  /// use ronkathon::hashes::sha512::Sha512;
  ///
  /// let input = b"abc";
  /// let output = Sha512::digest(input);
  /// assert_eq!(
  ///   hex::encode(output),
  ///   "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
  /// );
  /// ```

  pub fn digest(input: &[u8]) -> [u8; 64] {
    ///////////////////////////////////////////////////////////////////////////
    // Set up initial data structures.
    //
    // Initialize the hash values.
    // This will be the variable we update as we process the input.
    let mut hash = H;

    // Initialize the array of message words which will be used in the hash computation.
    let mut words = [0u64; 80];

    ///////////////////////////////////////////////////////////////////////////
    // Padding
    //
    // The message is padded so that its length is congruent to 896 modulo 1024.
    // The padding consists of a single 1 bit followed by zeros, and the length
    // of the message in bits is appended to the end.
    let len = input.len() as u64 * 8;
    let len_with_1_appended = len + 1;
    let len_mod = len_with_1_appended % 1024;
    let zero_padding = if len_mod > 896 { 1024 + 896 - len_mod } else { 896 - len_mod };
    let len_padded = (len_with_1_appended as usize + zero_padding as usize) / 8;

    // Create the padded message from the input.
    let mut message = Vec::with_capacity(len_padded);
    message.extend_from_slice(input);

    // Push on the 1 bit followed by zeroes.
    message.push(0x80);

    // Push on the remaining needed zeroes we computed above.
    message.extend(&vec![0; len_padded - len as usize / 8 - 1]);

    // Push on the length of the message in bits.
    message.extend(&vec![0; 8]);
    message.extend_from_slice(&len.to_be_bytes());
    ///////////////////////////////////////////////////////////////////////////

    ///////////////////////////////////////////////////////////////////////////
    // Hashing
    //
    // Process the message in 1024-bit blocks.
    for chunk in message.chunks(128) {
      // Copy the bytes into the words array to fill the first 16 words.
      for i in 0..16 {
        words[i] = u64::from_be_bytes([
          chunk[i * 8],
          chunk[i * 8 + 1],
          chunk[i * 8 + 2],
          chunk[i * 8 + 3],
          chunk[i * 8 + 4],
          chunk[i * 8 + 5],
          chunk[i * 8 + 6],
          chunk[i * 8 + 7],
        ]);
      }

      // Use our permutations/compression functions to complete the block
      // decomposition for the remaining words.
      for i in 16..80 {
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
      for i in 0..80 {
        let temp1 = h
          .wrapping_add(sigma_1(e))
          .wrapping_add(ch(e, f, g))
          .wrapping_add(K[i])
          .wrapping_add(words[i]);
        let temp2 = sigma_0(a).wrapping_add(maj(a, b, c));

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

    // Convert the hash to a byte array with correct endianness and
    // type then return it.
    hash.iter_mut().for_each(|x| *x = x.to_be());
    unsafe { std::mem::transmute(hash) }
  }
}

#[cfg(test)]
mod tests {

  use hex_literal::hex;
  use rstest::rstest;

  use super::*;

  #[rstest]
  #[case(b"", hex!["cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"])]
  #[case(b"abc", hex!["ddaf35a193617aba cc417349ae204131 12e6fa4e89a97ea2 0a9eeee64b55d39a 2192992a274fc1a8 36ba3c23a3feebbd 454d4423643ce80e 2a9ac94fa54ca49f"])]
  #[case(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", hex!["204a8fc6dda82f0a 0ced7beb8e08a416 57c16ef468b228a8 279be331a703c335 96fd15c13b1b07f9 aa1d3bea57789ca0 31ad85c7a71dd703 54ec631238ca3445"])]
  #[case(b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu", hex!["8e959b75dae313da 8cf4f72814fc143f 8f7779c6eb9f7fa1 7299aeadb6889018 501d289e4900f7e4 331b99dec4b5433a c7d329eeb6dd2654 5e96e55b874be909"])]
  fn test_sha512(#[case] input: &[u8], #[case] expected: [u8; 64]) {
    assert_eq!(Sha512::digest(input), expected);
  }
}
