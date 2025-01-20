use super::MlKemField;
use crate::algebra::field::Field;

/// Encodes a field element into a byte array where each field element is represented by D bits.
/// Converts the field element into a binary representation and then packs the bits into bytes.
fn byte_encode<const D: usize>(f: [MlKemField; 256]) -> [u8; 32 * D]
where [(); 256 * D]: {
  let mut encoded_bits = [0u8; 256 * D];

  for (i, x) in f.iter().enumerate() {
    let mut val = x.value;
    for j in 0..D {
      encoded_bits[i * D + j] = (val & 1) as u8;
      val >>= 1;
    }
  }

  let mut encoded_bytes = [0u8; 32 * D];
  for (i, chunk) in encoded_bits.chunks(8).enumerate() {
    encoded_bytes[i] = chunk.iter().enumerate().fold(0, |acc, (j, &b)| acc | (b << j));
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
fn byte_decode<const D: usize>(encoded_bytes: [u8; 32 * D]) -> [MlKemField; 256]
where [(); 256 * D]: {
  let mut encoded_bits = [0u8; 256 * D];
  for (i, &byte) in encoded_bytes.iter().enumerate() {
    for j in 0..8 {
      encoded_bits[i * 8 + j] = (byte >> j) & 1;
    }
  }

  let mut f = [MlKemField::ZERO; 256];
  for (i, chunk) in encoded_bits.chunks(D).enumerate() {
    let mut val = 0;
    for (j, &bit) in chunk.iter().enumerate() {
      val |= (bit as usize) << j;
    }
    f[i].value = val;
  }

  f
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
    let encoded = byte_encode::<8>(f);
    let encoded_optimized = byte_encode_optimized::<8>(f);
    assert_eq!(encoded, encoded_optimized);
  }

  #[bench]
  fn bench_byte_encode(b: &mut test::Bencher) {
    let f = generate_test_data();
    b.iter(|| byte_encode::<8>(f));
  }

  #[bench]
  fn bench_byte_encode_optimized(b: &mut test::Bencher) {
    let f = generate_test_data();
    b.iter(|| byte_encode_optimized::<8>(f));
  }
}
