//! Implements the SHA hash functions. Currently we implement SHA-256, SHA-512.
//! References:
//! [SHS]: "Secure Hash Standard", National Institute of Science and Technology, Federal Information Processing Standard (FIPS) 180-3, https://csrc.nist.gov/files/pubs/fips/180-3/final/docs/fips180-3_final.pdf.
use std::marker::PhantomData;

use num_traits::{FromBytes, PrimInt, ToBytes, WrappingAdd};

type Fn1<T> = fn(T) -> T;
type Fn2<T> = fn(T, T, T) -> T;

struct ShaFuncs<T> {
  pub ch:            Fn2<T>,
  pub maj:           Fn2<T>,
  pub small_sigma_0: Fn1<T>,
  pub small_sigma_1: Fn1<T>,
  pub sigma_0:       Fn1<T>,
  pub sigma_1:       Fn1<T>,
}

const fn rotate_right<T, const N: usize>(x: T) -> T
where T: PrimInt {
  (x >> N) | (x << (std::mem::size_of::<T>() * 8 - N))
}

struct Funcs<T> {
  pd: PhantomData<T>,
}

/// Generic implementation of functions used in SHA hash computation.
impl<T> Funcs<T>
where T: PrimInt
{
  /// The [Ch](https://csrc.nist.gov/files/pubs/fips/180-3/final/docs/fips180-3_final.pdf) function used in SHA-256 & SHA-512.
  /// This is a logical function used in the hash computation used to "choose" between `y` and `z`
  /// given `x` as a conditional.
  pub fn ch(x: T, y: T, z: T) -> T { (x & y) ^ (!x & z) }

  /// The [Maj](https://csrc.nist.gov/files/pubs/fips/180-3/final/docs/fips180-3_final.pdf) function used in SHA-256 and SHA-512.
  /// This is a logical function used in the hash computation used to select the "majority" of the
  /// values of `x`, `y`, and `z`.
  pub fn maj(x: T, y: T, z: T) -> T { (x & y) ^ (x & z) ^ (y & z) }

  /// Generic [Σ0 and Σ1](https://csrc.nist.gov/files/pubs/fips/180-3/final/docs/fips180-3_final.pdf) functions used in SHA-256 & SHA-512.
  /// This is used as a compression function in the hash computation.
  pub fn sigma<const A: usize, const B: usize, const C: usize>(x: T) -> T {
    rotate_right::<T, A>(x) ^ rotate_right::<T, B>(x) ^ rotate_right::<T, C>(x)
  }

  /// Generic [σ0 and σ1](https://csrc.nist.gov/files/pubs/fips/180-3/final/docs/fips180-3_final.pdf) functions used in SHA-256 & SHA-512.
  /// This is used as a message schedule functions in the hash computation.
  pub fn small_sigma<const A: usize, const B: usize, const C: usize>(x: T) -> T {
    rotate_right::<T, A>(x) ^ rotate_right::<T, B>(x) ^ (x >> C)
  }
}

/// A generic SHA hash function.
pub struct SHA<T, const N: usize, const ROUNDS: usize> {
  k:     [T; ROUNDS],
  h:     [T; 8],
  funcs: ShaFuncs<T>,
}

impl<T, const N: usize, const ROUNDS: usize> SHA<T, N, ROUNDS> {
  /// The SHA hash function.
  /// This function takes an input byte array and returns a byte array representing the hash
  /// of the input.
  ///
  /// # Arguments
  /// * `input` - A byte array representing the input to the hash function.
  ///
  /// # Returns
  /// A byte array representing the hash of the input, which is of length 32 bytes if Sha256 is
  /// used and 64 if Sha512 is used.
  ///
  /// # Example
  /// ```
  /// use hex;
  /// use ronkathon::hashes::sha::Sha256;
  ///
  /// let input = b"abc";
  /// let hash = Sha256::new();
  /// let output = hash.digest(input);
  /// assert_eq!(
  ///   hex::encode(output),
  ///   "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  /// );
  /// ```
  pub fn digest(&self, input: &[u8]) -> Vec<u8>
  where T: PrimInt
      + Default
      + WrappingAdd
      + ToBytes<Bytes = [u8; std::mem::size_of::<T>()]>
      + FromBytes<Bytes = [u8; std::mem::size_of::<T>()]> {
    ///////////////////////////////////////////////////////////////////////////
    // Set up initial data structures.
    //
    // Initialize the hash values.
    // This will be the variable we update as we process the input.
    let mut hash = self.h;

    // Initialize the array of message words which will be used in the hash computation.
    let mut words = [T::default(); ROUNDS];

    ///////////////////////////////////////////////////////////////////////////
    // Padding
    //
    // The message is padded so that its length is congruent to `p` modulo `block_size`.
    // The padding consists of a single 1 bit followed by zeros, and the length
    // of the message in bits is appended to the end.
    let block_size: usize = N * 2;
    let p: usize = block_size - N / 4;

    let len = input.len() * 8;
    let len_with_1_appended = len + 1;
    let len_mod = len_with_1_appended % block_size;
    let zero_padding = if len_mod > p { block_size + p - len_mod } else { p - len_mod };
    let len_padded = (len_with_1_appended + zero_padding) / 8;

    // Create the padded message from the input.
    let mut message = Vec::with_capacity(len_padded);
    message.extend_from_slice(input);

    // Push on the 1 bit followed by zeroes.
    message.push(0x80);

    // Push on the remaining needed zeroes we computed above.
    message.extend(&vec![0; len_padded - len / 8 - 1]);

    // Push on the length of the message in bits.
    message.extend(&vec![0; (N / 4 - 64) / 8]);
    message.extend_from_slice(&len.to_be_bytes());
    ///////////////////////////////////////////////////////////////////////////

    ///////////////////////////////////////////////////////////////////////////
    // Hashing
    //
    // Process the message in `block_size` bit blocks.
    for block in message.chunks(N / 4) {
      // Copy the bytes into the words array to fill the first 16 words.
      let size = std::mem::size_of::<T>();
      for (i, word) in block.chunks(size).enumerate() {
        words[i] = T::from_be_bytes(word.try_into().unwrap());
      }

      // Use our permutations/compression functions to complete the block
      // decomposition for the remaining words.
      for i in 16..ROUNDS {
        words[i] = (self.funcs.small_sigma_1)(words[i - 2])
          .wrapping_add(&words[i - 7])
          .wrapping_add(&(self.funcs.small_sigma_0)(words[i - 15]))
          .wrapping_add(&words[i - 16]);
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
      for (i, word) in words.iter().enumerate() {
        let temp1 = h
          .wrapping_add(&(self.funcs.sigma_1)(e))
          .wrapping_add(&(self.funcs.ch)(e, f, g))
          .wrapping_add(&self.k[i])
          .wrapping_add(word);
        let temp2 = (self.funcs.sigma_0)(a).wrapping_add(&(self.funcs.maj)(a, b, c));

        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(&temp1);
        d = c;
        c = b;
        b = a;
        a = temp1.wrapping_add(&temp2);
      }

      // Update the hash values.
      hash[0] = hash[0].wrapping_add(&a);
      hash[1] = hash[1].wrapping_add(&b);
      hash[2] = hash[2].wrapping_add(&c);
      hash[3] = hash[3].wrapping_add(&d);
      hash[4] = hash[4].wrapping_add(&e);
      hash[5] = hash[5].wrapping_add(&f);
      hash[6] = hash[6].wrapping_add(&g);
      hash[7] = hash[7].wrapping_add(&h);
    }

    // Convert the hash to a byte array with correct endianness and
    // type then return it.
    let mut h: Vec<u8> = vec![];
    for hi in &hash {
      h.extend(hi.to_be_bytes());
    }
    h
  }
}

/// The SHA-256 hash function
pub type Sha256 = SHA<u32, 256, 64>;

impl Sha256 {
  /// Creates a new instance of `Sha256` object
  pub const fn new() -> Self {
    SHA {
      h:     [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
      ],
      k:     [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
      ],
      funcs: ShaFuncs::<u32> {
        ch:            Funcs::<u32>::ch,
        maj:           Funcs::<u32>::maj,
        small_sigma_0: Funcs::<u32>::small_sigma::<7, 18, 3>,
        small_sigma_1: Funcs::<u32>::small_sigma::<17, 19, 10>,
        sigma_0:       Funcs::<u32>::sigma::<2, 13, 22>,
        sigma_1:       Funcs::<u32>::sigma::<6, 11, 25>,
      },
    }
  }
}

/// The SHA-512 hash function
pub type Sha512 = SHA<u64, 512, 80>;

impl Sha512 {
  /// Creates a new instance of Sha512 object, which implement SHA-512 hash function.
  pub const fn new() -> Self {
    SHA {
      h:     [
        0x6A09E667F3BCC908,
        0xBB67AE8584CAA73B,
        0x3C6EF372FE94F82B,
        0xA54FF53A5F1D36F1,
        0x510E527FADE682D1,
        0x9B05688C2B3E6C1F,
        0x1F83D9ABFB41BD6B,
        0x5BE0CD19137E2179,
      ],
      funcs: ShaFuncs::<u64> {
        ch:            Funcs::<u64>::ch,
        maj:           Funcs::<u64>::maj,
        small_sigma_0: Funcs::<u64>::small_sigma::<1, 8, 7>,
        small_sigma_1: Funcs::<u64>::small_sigma::<19, 61, 6>,
        sigma_0:       Funcs::<u64>::sigma::<28, 34, 39>,
        sigma_1:       Funcs::<u64>::sigma::<14, 18, 41>,
      },
      k:     [
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
      ],
    }
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
    let hash = Sha512::new();
    assert_eq!(hash.digest(input), expected);
  }

  #[rstest]
  #[case(b"abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")]
  #[case(
    b"abcdefghijklmnopqrstuvwxyz0123456789",
    "011fc2994e39d251141540f87a69092b3f22a86767f7283de7eeedb3897bedf6"
  )]
  #[case(
            b"Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.",
            "2d8c2f6d978ca21712b5f6de36c9d31fa8e96a4fa5d8ff8b0188dfb9e7c171bb"
        )]
  #[case(b"", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")]
  fn test_sha256(#[case] input: &[u8], #[case] expected: &str) {
    let hash = Sha256::new();
    assert_eq!(hex::encode(hash.digest(input)), expected);
  }
}
