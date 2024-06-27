use des::{
  cipher::{generic_array::GenericArray, BlockDecrypt, BlockEncrypt, KeyInit},
  Des as Des_fuzz,
};
use rand::{thread_rng, Rng};

use super::{left_shift, *};

fn exhaustive_key_search(
  ciphertext: &[u8; 8],
  plaintext: &[u8; 8],
  ciphertext2: &[u8; 8],
  plaintext2: &[u8; 8],
) -> Option<[u8; 8]> {
  for k in 0..(1u64 << 56) {
    let key = k.to_be_bytes();
    let subkeys = DES::setup(key);

    let decrypted = DES::decrypt(&subkeys, ciphertext);
    let decrypted2 = DES::decrypt(&subkeys, ciphertext2);

    if decrypted == *plaintext && decrypted2 == *plaintext2 {
      return Some(key);
    }
  }
  None
}

#[test]
/// use multiple keys for more confidence
fn known_plaintext_attack() {
  let mut rng = thread_rng();
  let plaintext1 = rng.gen();
  let plaintext2 = rng.gen();

  let key = 100000_u64.to_be_bytes();

  let subkeys = DES::setup(key);

  let ciphertext = DES::encrypt(&subkeys, &plaintext1);
  let ciphertext2 = DES::encrypt(&subkeys, &plaintext2);

  let attack_key = exhaustive_key_search(&ciphertext, &plaintext1, &ciphertext2, &plaintext2);

  assert!(attack_key.is_some());
}

#[test]
fn des() {
  for _ in 0..100 {
    let mut rng = thread_rng();
    let secret_key = rng.gen();

    let subkeys = DES::setup(secret_key);

    let message = rng.gen();
    let encrypted = DES::encrypt(&subkeys, &message);
    let decrypted = DES::decrypt(&subkeys, &encrypted);

    assert_eq!(message, decrypted);
  }
}

#[test]
fn des_fuzz() {
  let mut rng = thread_rng();
  let key: [u8; 8] = rng.gen();

  let subkeys = DES::setup(key);
  let des_fuzz = Des_fuzz::new_from_slice(&key).unwrap();

  let mut data: [u8; 8] = rng.gen();

  let encrypted = DES::encrypt(&subkeys, &data);
  des_fuzz.encrypt_block(GenericArray::from_mut_slice(&mut data));

  let decrypted = DES::decrypt(&subkeys, &encrypted);
  des_fuzz.decrypt_block(GenericArray::from_mut_slice(&mut data));

  assert_eq!(decrypted, data);
}

#[test]
/// DES has four weak keys where encryption and decryption are same.
/// This is only possible when all round keys are same.
fn weak_keys() {
  const WEAK_KEYS: [[u8; 8]; 4] = [
    [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
    [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
    [0x1F, 0x1F, 0x1F, 0x1F, 0x0E, 0x0E, 0x0E, 0x0E],
    [0xE0, 0xE0, 0xE0, 0xE0, 0xF1, 0xF1, 0xF1, 0xF1],
  ];

  for key in WEAK_KEYS.into_iter() {
    let subkeys = DES::setup(key);

    let message = b"weaktest";

    let encrypted = DES::encrypt(&subkeys, message);
    let decrypted = DES::decrypt(&subkeys, message);

    assert_eq!(encrypted, decrypted);
  }
}

#[test]
/// DES has a nice property where $y=ENC_k(x)$ and $y'=ENC_{k'}(x')$
fn bit_complement() {
  let mut rng = thread_rng();
  let secret_key: u64 = rng.gen();

  let subkeys = DES::setup(secret_key.to_be_bytes());

  let message: u64 = rng.gen();
  let encrypted = DES::encrypt(&subkeys, &message.to_be_bytes());

  let key_complement = u64::MAX ^ secret_key;
  let message_complement = u64::MAX ^ message;

  let subkeys_complement = DES::setup(key_complement.to_be_bytes());
  let encrypted_complement = DES::encrypt(&subkeys_complement, &message_complement.to_be_bytes());

  assert_eq!(u64::MAX ^ u64::from_be_bytes(encrypted), u64::from_be_bytes(encrypted_complement));
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
