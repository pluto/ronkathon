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
    let des = DES::new(key).unwrap();
    let decrypted = des.decrypt(ciphertext);
    let decrypted2 = des.decrypt(ciphertext2);

    if decrypted == Ok(*plaintext) && decrypted2 == Ok(*plaintext2) {
      return Some(key);
    }
  }
  None
}

#[test]
/// use multiple keys for more confidence
fn known_plaintext_attack() {
  let mut rng = thread_rng();
  let mut plaintext1 = [0u8; 8];
  rng.fill(&mut plaintext1);
  let mut plaintext2 = [0u8; 8];
  rng.fill(&mut plaintext2);

  let key = 100000_u64.to_be_bytes();

  let des = DES::new(key).unwrap();

  let ciphertext = des.encrypt(&plaintext1).unwrap();
  let ciphertext2 = des.encrypt(&plaintext2).unwrap();

  let attack_key = exhaustive_key_search(&ciphertext, &plaintext1, &ciphertext2, &plaintext2);

  assert!(attack_key.is_some());
}

#[test]
fn des() {
  for _ in 0..100 {
    let mut rng = thread_rng();
    let secret_key = rng.gen();

    let des = DES::new(secret_key).unwrap();

    let message = rng.gen();
    let encrypted = des.encrypt(&message).unwrap();
    let decrypted = des.decrypt(&encrypted).unwrap();

    assert_eq!(message, decrypted);
  }
}

#[test]
fn des_fuzz() {
  let mut rng = thread_rng();
  let key: [u8; 8] = rng.gen();

  let des_fuzz = DES::new(key).unwrap();

  let data: [u8; 8] = rng.gen();

  let encrypted = des_fuzz.encrypt(&data).unwrap();

  let decrypted = des_fuzz.decrypt(&encrypted).unwrap();

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
    let des = DES::new(key).unwrap();

    let message = b"weaktest";

    let encrypted = des.encrypt(message);
    let decrypted = des.decrypt(message);

    assert_eq!(encrypted, decrypted);
  }
}

#[test]
/// DES has a nice property where $y=ENC_k(x)$ and $y'=ENC_{k'}(x')$
fn bit_complement() {
  let mut rng = thread_rng();
  let secret_key: u64 = rng.gen();

  let des = DES::new(secret_key.to_be_bytes()).unwrap();

  let message: u64 = rng.gen();
  let encrypted = des.encrypt(&message.to_be_bytes()).unwrap();

  let key_complement = u64::MAX ^ secret_key;
  let message_complement = u64::MAX ^ message;

  let des_complement = DES::new(key_complement.to_be_bytes()).unwrap();
  let encrypted_complement = des_complement.encrypt(&message_complement.to_be_bytes()).unwrap();

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
