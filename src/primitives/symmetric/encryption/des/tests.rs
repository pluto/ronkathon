use des::cipher::{generic_array::GenericArray, BlockDecrypt, BlockEncrypt, KeyInit};
use rand::{thread_rng, Rng};

use super::{left_shift, *};

#[test]
fn des() {
  for _ in 0..100 {
    let mut rng = thread_rng();
    let secret_key = rng.gen();

    let des = Des::new(secret_key);

    let message = rng.gen();
    let encrypted = des.encrypt(&message);
    let decrypted = des.decrypt(&encrypted);

    assert_eq!(message, decrypted);
  }
}

#[test]
fn des_fuzz() {
  let mut rng = thread_rng();
  let key: [u8; 8] = rng.gen();

  let des = Des::new(key);
  let des_fuzz = des::Des::new_from_slice(&key).unwrap();

  let mut data: [u8; 8] = rng.gen();

  let encrypted = des.encrypt(&data);
  des_fuzz.encrypt_block(GenericArray::from_mut_slice(&mut data));

  let decrypted = des.decrypt(&encrypted);
  des_fuzz.decrypt_block(GenericArray::from_mut_slice(&mut data));

  assert_eq!(decrypted, data);
}

#[test]
fn test_left_shift() {
  // data = 00000101 11110101 11100001 00011001
  let data = 100000025_u32.to_be_bytes();

  // shift = 00000111 11010111 10000100 01100101
  let shifts = left_shift(&data, 2);

  assert_eq!(shifts[0], 0b00000111);
  assert_eq!(shifts[1], 0b11010111);
  assert_eq!(shifts[2], 0b10000100);
  assert_eq!(shifts[3], 0b01100101);
}

#[test]
fn test_get_byte_from_bits() {
  let data = [1, 0, 1, 1, 0, 1, 0, 0];
  let res = 0b10110100_u8;
  assert_eq!(get_byte_from_bits(&data), res);
}
