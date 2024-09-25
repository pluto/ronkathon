//! Implementation of [`GHASH`] algorithm which is used in AES-GCM to compute the authentication
//! tag.
//! Based on GCM specification given by NIST:
//! [The Galois/Counter Mode of Operation (GCM)](http://www.csrc.nist.gov/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-revised-spec.pdf)
//!
//! ASCII diagram of GHASH, courtesy of @0xJepsen:
//!           X1                      X2          ...          XM
//!           |                       |                        |
//!           |                       v                        v
//!           |                  ------------             ------------
//!           |           ------>|   XOR    |      ------>|   XOR    |
//!           |           |      -----┬------      |      -----┬------
//!           |           |           |            |           |
//!           v           |           v            |           v
//!  ------------------   |   ------------------   |   ------------------
//!  | multiply by H  |   |   | multiply by H  |   |   | multiply by H  |
//!  ---------┬--------   |   --------┬---------   |   --------┬---------
//!           |           |           |            |           |
//!           v           |           v            |           v
//!      -----------      |      -----------       |      -----------
//!      |  TAG1   | ------      |   TAG2  | -------      |   TAGM  |
//!      -----------             -----------              -----------

use core::array;

use super::constants::GCMF_IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS;
use crate::{
  algebra::field::{extension::GaloisField, prime::AESField},
  polynomial::{Monomial, Polynomial},
  Field,
};

type GCMField = GaloisField<128, 2>;
/// Note: ['AESField'] is an alias for [`PrimeField<2>`]

/// Helper function which turns [`num`], u64, value to vector of [`AESField`] elements
/// The result is aligned to [`length`] by padding with AESField::ZERO.
/// For example:
/// If num = 5 and length = 8, the result is:
/// {ZERO, ZERO, ZERO, ZERO, ZERO, ONE, ZERO, ONE}
/// where the rightmost value is the least significant bit(=2^0)
/// and `ZERO` and `ONE` are `AESField` elements.
fn to_bool_vec(mut num: u64, length: usize) -> Vec<AESField> {
  let mut result = vec![AESField::ZERO; length];
  let mut idx = length;
  while num > 0 {
    result[idx - 1] = match num & 1 {
      0 => AESField::ZERO,
      _ => AESField::ONE,
    };
    num >>= 1;
    idx -= 1;
  }
  result
}

/// Convert bytes(a slice of u8 value) to GCMField element.
impl From<&[u8]> for GCMField {
  fn from(value: &[u8]) -> Self {
    let mut result = Vec::<AESField>::new();
    for &b in value.iter() {
      let b_f: Vec<AESField> = to_bool_vec(b as u64, 8);
      result.extend(b_f);
    }
    result.extend(std::iter::repeat(AESField::ZERO).take(128 - value.len() * 8));
    Self { coeffs: result.try_into().unwrap() }
  }
}

/// Convert a GCMField element to a vector of u8 values.
impl From<GCMField> for Vec<u8> {
  fn from(value: GCMField) -> Self {
    let mut bytes = Vec::new();
    for block in value.coeffs.chunks(8) {
      let mut byte: u8 = 0;
      for (i, &b) in block.iter().take(8).enumerate() {
        if b == AESField::ONE {
          byte += (1 << (7 - i)) as u8;
        }
      }
      bytes.push(byte);
    }
    bytes
  }
}

/// Represents the GHASH object which holds `hash_key`, a GCMField element, which in
/// context of AES-GCM is equal to E(K, 0^128), where E is AES encryption and K, the key.
pub struct GHASH {
  hash_key: GCMField,
}

impl GHASH {
  /// Construct GHASH object using 'h', the hash key(in bytes).
  /// In context of AES-GCM, h = AES(K, 0^128), that is enc 128-bit string of zeros
  /// encrypted using AES.
  pub fn new(h: &[u8]) -> Self {
    if h.len() != 16 {
      panic!("The hash key should be 128-bits, or 16 u8 values! Got {} u8 vals", h.len());
    }
    Self { hash_key: GCMField::from(h) }
  }

  /// Get the hash digest using using two u8 slices `a` and `c`.
  /// In context of AES-GCM they correspond to,
  /// 'aad' - additional authenticated data(AAD)
  /// 'ct' - ciphertext encrypted using AES.
  ///
  /// The result is a 128-bit digest, returned as an `[u8; 16]` array.
  pub fn digest(&self, aad: &[u8], ct: &[u8]) -> [u8; 16] {
    // The variable where the final digest is accumulated.
    let mut j = GCMField::default();

    // Process each 16-byte block from the aad
    for block in aad.chunks(16) {
      let a = GCMField::from(block);
      // ADD a block of `aad` into the result and then MULTIPLY with hash_key.
      // ADD interestingly is same as XOR in our field.
      // MULTIPLY is a polynomial multiplication modulo a fixed field polynomial. See
      // `poly_multiply`
      j = Self::poly_multiply(a + j, self.hash_key);
    }

    // Do the same stuff as the previous loop but with ciphertext.
    for block in ct.chunks(16) {
      let a = GCMField::from(block);
      j = Self::poly_multiply(a + j, self.hash_key);
    }

    // The final block consists of length of `aad` in bits and length of `ct` in bits, each in
    // 64-bit format.
    let mut aad_len = to_bool_vec((aad.len() * 8) as u64, 64);
    let mut ct_len = to_bool_vec((ct.len() * 8) as u64, 64);
    aad_len.append(&mut ct_len);
    let len = GCMField { coeffs: aad_len.try_into().unwrap() };
    j = Self::poly_multiply(j + len, self.hash_key);

    let j_bytes: Vec<u8> = j.into();
    j_bytes.try_into().unwrap()
  }

  /// Returns the result of multiplication of two GCMField elements,
  /// modulo the field polynomial, f = 1 + α + α^2 + α^7 + α^128
  fn poly_multiply(x: GCMField, y: GCMField) -> GCMField {
    let x_coeffs: [AESField; 128] = x.coeffs;
    let y_coeffs: [AESField; 128] = y.coeffs;
    let poly_x = Polynomial::<Monomial, AESField, 128>::from(x_coeffs);
    let poly_y = Polynomial::<Monomial, AESField, 128>::from(y_coeffs);
    let poly_f =
      Polynomial::<Monomial, AESField, 129>::from(GCMF_IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS);

    let poly_z = (poly_x * poly_y) % poly_f;
    let res: [AESField; 128] =
      array::from_fn(|i| poly_z.coefficients.get(i).cloned().unwrap_or(AESField::ZERO));

    GCMField::new(res)
  }

  /// Multiply two elements in GCMField modulo the field polynomial f.
  /// The field polynomial is fixed and is given by, f = 1 + α + α^2 + α^7 + α^128
  /// The function uses the algorithm given in the GCM spec.
  /// NOTE: We do not use this function in our GHASH algorithm, it is for reference only.
  #[allow(dead_code)]
  fn poly_multiply_spec(x: GCMField, y: GCMField) -> GCMField {
    let mut r_coeffs = to_bool_vec(0xe1, 128);
    r_coeffs.rotate_left(120);
    let r = GCMField { coeffs: r_coeffs.try_into().unwrap() };

    let mut z = GCMField::from(0_usize);
    let mut v = y;

    for bit in x.coeffs {
      if bit == AESField::ONE {
        z += v;
      }

      let mut v1 = v.coeffs.to_vec();
      let v1_bit = v1.pop().unwrap();
      v1.push(AESField::ZERO);
      v1.rotate_right(1);

      v = GCMField { coeffs: v1.try_into().unwrap() };

      if v1_bit == AESField::ONE {
        v += r;
      }
    }

    z
  }
}

#[cfg(test)]
mod tests {
  use core::str;
  use std::{fmt::Write, num::ParseIntError};

  use rstest::rstest;

  use super::*;
  pub fn decode_hex(s: &str) -> Result<Vec<u8>, ParseIntError> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16)).collect()
  }

  pub fn encode_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
      write!(&mut s, "{:02x}", b).unwrap();
    }
    s
  }

  // Tests against NIST test vectors in [GCM spec](https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-revised-spec.pdf)
  #[rstest]
  // NIST Test Case #1
  #[case("66e94bd4ef8a2c3b884cfa59ca342b2e", "", "", "00000000000000000000000000000000")]
  // NIST Test Case #2
  #[case(
    "66e94bd4ef8a2c3b884cfa59ca342b2e",
    "",
    "0388dace60b6a392f328c2b971b2fe78",
    "f38cbb1ad69223dcc3457ae5b6b0f885"
  )]
  // NIST Test Case #3
  #[case(
    "b83b533708bf535d0aa6e52980d53b78",
    "",
    "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985",
    "7f1b32b81b820d02614f8895ac1d4eac"
    )]
  // NIST Test Case #4
  #[case(
    "b83b533708bf535d0aa6e52980d53b78",
    "feedfacedeadbeeffeedfacedeadbeefabaddad2",
    "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091",
    "698e57f70e6ecc7fd9463b7260a9ae5f",
    )]
  // NIST Test Case #6
  #[case(
    "b83b533708bf535d0aa6e52980d53b78",
    "feedfacedeadbeeffeedfacedeadbeefabaddad2",
    "8ce24998625615b603a033aca13fb894be9112a5c3a211a8ba262a3cca7e2ca701e4a9a4fba43c90ccdcb281d48c7c6fd62875d2aca417034c34aee5",
    "1c5afe9760d3932f3c9a878aac3dc3de",
      )]
  fn test_ghash(#[case] hx: &str, #[case] ax: &str, #[case] cx: &str, #[case] expected: &str) {
    let h = decode_hex(hx).unwrap();
    let a = decode_hex(ax).unwrap();
    let c = decode_hex(cx).unwrap();

    let gh = GHASH::new(&h);
    let digest = gh.digest(&a, &c);

    let digest_hex = encode_hex(&digest);

    println!("GHASH:{}\nExpected:{}", digest_hex, expected);
    assert!(digest_hex == expected);
  }

  #[rstest]
  #[case(1, 1)]
  #[case(2, 3)]
  #[case(113, 117)]
  #[case(0xca, 0xfe)]
  fn test_poly_multiply(#[case] x: u64, #[case] y: u64) {
    let x_coeffs: Vec<AESField> = to_bool_vec(x, 128).into_iter().rev().collect();
    let xf = GCMField { coeffs: x_coeffs.try_into().unwrap() };
    let y_coeffs = to_bool_vec(y, 128);
    let yf = GCMField { coeffs: y_coeffs.try_into().unwrap() };

    let zf = GHASH::poly_multiply(xf, yf);

    let z_coeffs: Vec<u8> = zf.into();
    let z_hex = encode_hex(&z_coeffs);

    let expected_zf = GHASH::poly_multiply_spec(xf, yf);
    let expected_z_coeffs: Vec<u8> = expected_zf.into();
    let expected_z_hex = encode_hex(&expected_z_coeffs);

    println!("Got: {z_hex}\nExp: {expected_z_hex}");
    assert!(expected_z_hex == z_hex);
  }
}
