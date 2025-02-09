use super::{MlKemField, PolyVec};
use crate::{
  algebra::field::Field,
  polynomial::{Basis, Polynomial},
};

/// Encodes a field element into a byte array where each field element is represented by d bits.
/// Converts the field element into a binary representation and then packs the bits into bytes.
pub fn byte_encode<const d: usize, const D: usize>(f: &[MlKemField; D]) -> Vec<u8> {
  let mut encoded_bits = Vec::with_capacity(D * d);

  for (i, x) in f.iter().enumerate() {
    let mut val = x.value;
    for j in 0..d {
      encoded_bits[i * d + j] = (val & 1) as u8;
      val >>= 1;
    }
  }

  let mut encoded_bytes = Vec::with_capacity(D / 8 * d);
  for (i, chunk) in encoded_bits.chunks(8).enumerate() {
    encoded_bytes[i] = chunk.iter().enumerate().fold(0, |acc, (j, &b)| acc | (b << j));
  }

  encoded_bytes
}

pub fn byte_encode_polyvec<B: Basis, const D: usize, const K: usize, const d: usize>(
  f: PolyVec<B, D, K>,
) -> Vec<u8> {
  let mut encoded_bytes = Vec::with_capacity(D / 8 * d * K);
  for (i, poly) in f.vec.iter().enumerate() {
    let encoded = byte_encode::<d, D>(&poly.coefficients);
    encoded_bytes[i * D / 8 * d..(i + 1) * D / 8 * d].copy_from_slice(&encoded);
  }

  encoded_bytes
}

/// Encodes a field element into a byte array where each field element is represented by D bits.
/// Converts the field element into a binary representation and then packs the bits into bytes.
fn byte_encode_optimized<const D: usize>(f: [MlKemField; 256]) -> [u8; 32 * D]
where [(); 256 * D]: {
  let mut encoded_bytes = [0u8; 32 * D];

  // Process 8 field elements at a time to fill each D bytes
  for chunk_idx in 0..32 {
    let chunk_start = chunk_idx * 8;
    let elements = &f[chunk_start..chunk_start + 8];

    // For each bit position within the D bits
    for bit_pos in 0..D {
      let byte_idx = chunk_idx * D + bit_pos;

      // Collect bits from 8 elements into a single byte
      encoded_bytes[byte_idx] = elements
        .iter()
        .enumerate()
        .fold(0, |acc, (j, x)| acc | (((x.value >> bit_pos) & 1) as u8) << j);
    }
  }

  encoded_bytes
}

/// Decodes a byte array into a field element where each field element is represented by D bits.
/// Unpacks the bytes into bits and then converts the bits into a field element.
pub fn byte_decode<const d: usize, const D: usize>(encoded_bytes: &[u8]) -> [MlKemField; D] {
  let mut encoded_bits = Vec::with_capacity(256 * d);
  for (i, &byte) in encoded_bytes.iter().enumerate() {
    for j in 0..8 {
      encoded_bits.push((byte >> j) & 1);
    }
  }

  let mask: usize = (1 << d) - 1;
  let mut f = [MlKemField::ZERO; D];
  for (i, chunk) in encoded_bits.chunks(D).enumerate() {
    let mut val = 0;
    for (j, &bit) in chunk.iter().enumerate() {
      val |= ((bit as usize) << j) & mask;
    }
    f[i].value = val;
  }

  f
}

pub fn byte_decode_polyvec<B: Basis, const D: usize, const K: usize, const d: usize>(
  encoded_bytes: &[u8],
  basis: B,
) -> PolyVec<B, D, K> {
  let mut f = Vec::with_capacity(K);

  for bytes in encoded_bytes.chunks(32 * d) {
    let coeffs = byte_decode::<d, D>(bytes.try_into().unwrap());
    f.push(Polynomial { coefficients: coeffs, basis: basis.clone() })
  }

  let f = f.try_into().unwrap();
  PolyVec::new(f)
}

#[cfg(test)]
mod tests {
  use super::*;
  extern crate test;

  fn generate_test_data() -> [MlKemField; 256] {
    let mut data = [MlKemField { value: 0 }; 256];
    for i in 0..256 {
      data[i].value = i as usize;
    }
    data
  }

  #[test]
  fn test_byte_encode() {
    let f = generate_test_data();
    let encoded = byte_encode::<8, 256>(&f);
    let encoded_optimized = byte_encode_optimized::<8>(f);
    assert_eq!(encoded, encoded_optimized);
  }

  #[bench]
  fn bench_byte_encode(b: &mut test::Bencher) {
    let f = generate_test_data();
    b.iter(|| byte_encode::<8, 256>(&f));
  }

  #[bench]
  fn bench_byte_encode_optimized(b: &mut test::Bencher) {
    let f = generate_test_data();
    b.iter(|| byte_encode_optimized::<8>(f));
  }
}
