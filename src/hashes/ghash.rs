use crate::{
  algebra::field::{extension::GaloisField, prime::AESField},
  Field,
};

type GCMField = GaloisField<128, 2>;

fn to_bool_vec(mut num: usize, length: usize) -> Vec<AESField> {
  let mut result = Vec::new();
  while num > 0 {
    result.push(match num & 1 {
      0 => AESField::ZERO,
      _ => AESField::ONE,
    });
    num >>= 1;
  }
  result.extend(std::iter::repeat(AESField::ZERO).take(length - result.len()));
  result
}

impl From<&[u8]> for GCMField {
  fn from(value: &[u8]) -> Self {
    let mut result = Vec::<AESField>::new();
    result.extend(std::iter::repeat(AESField::ZERO).take(128 - value.len() * 8));
    for &b in value.iter().rev() {
      let b_f: Vec<AESField> = to_bool_vec(b as usize, 8);
      result.extend(b_f);
    }
    Self { coeffs: result.try_into().unwrap() }
  }
}

impl From<GCMField> for Vec<u8> {
  fn from(value: GCMField) -> Self {
    let mut bytes = Vec::new();
    for block in value.coeffs.chunks(8) {
      let mut byte: u8 = 0;
      for i in 0..8 {
        if block[i] == AESField::ONE {
          byte += (1 << i) as u8;
        }
      }
      bytes.push(byte);
    }
    bytes.into_iter().rev().collect()
  }
}

/// Represents the GHASH object
pub struct GHASH {
  h: GCMField,
}

impl GHASH {
  /// Construct GHASH object using a bytes, which is generated usign AES128
  pub fn new(h_block: &[u8]) -> Self { Self { h: GCMField::from(h_block) } }

  /// Get the hash of bytes 'a' and 'c'
  pub fn digest(&self, a: &[u8], c: &[u8]) -> [u8; 16] {
    let mut j = GCMField::default();

    for block in a.chunks(16) {
      let a = GCMField::from(block);
      j = Self::poly_multiply(a + j, self.h);
    }

    for block in c.chunks(16) {
      let a = GCMField::from(block);
      j = Self::poly_multiply(a + j, self.h);
    }

    let mut a_len = to_bool_vec(a.len() * 8, 64);
    let mut c_len = to_bool_vec(c.len() * 8, 64);
    c_len.append(&mut a_len);
    let len = GCMField { coeffs: c_len.try_into().unwrap() };
    j = Self::poly_multiply(j + len, self.h);

    let j_bytes: Vec<u8> = j.into();
    j_bytes.try_into().unwrap()
  }

  /// Multiply two elements in GF(2^128) modulo a fixed polynomial =
  fn poly_multiply(x: GCMField, y: GCMField) -> GCMField {
    let mut r_coeffs = to_bool_vec(0xe1, 128);
    r_coeffs.rotate_right(120);
    let r = GCMField { coeffs: r_coeffs.try_into().unwrap() };

    let mut z = GCMField::from(0 as usize);
    let mut v = y;

    for &bit in x.coeffs.iter().rev() {
      if bit == AESField::ONE {
        z = z + v;
      }

      let mut v1 = v.coeffs.to_vec();
      v1.rotate_left(1);
      let v1_bit = v1.pop().unwrap();
      v1.push(AESField::ZERO);

      v = GCMField { coeffs: v1.try_into().unwrap() };

      if v1_bit == AESField::ONE {
        v = v + r;
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
  #[case(
    "66e94bd4ef8a2c3b884cfa59ca342b2e",
    "",
    "",
    "00000000000000000000000000000000"
      )]
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
}
