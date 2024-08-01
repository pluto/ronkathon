use super::*;

const PRIME_1: usize = 5;
const PRIME_2: usize = 3;
const PRIME_3: usize = 7;

#[test]
fn test_euler_totient() {
  assert_eq!(euler_totient(PRIME_1 as u64, PRIME_2 as u64), 8);
  assert_eq!(euler_totient(PRIME_2 as u64, PRIME_3 as u64), 12);
  assert_eq!(euler_totient(PRIME_3 as u64, PRIME_1 as u64), 24);
}

#[test]
fn key_gen() {
  let (rsa_encrypt, rsa_decrypt) = rsa_key_gen(PRIME_1, PRIME_2);
  assert_eq!(rsa_encrypt.public_key.n, PRIME_1 * PRIME_2);
  assert_eq!(
    gcd(rsa_decrypt.private_key.d as u64, euler_totient(PRIME_1 as u64, PRIME_2 as u64)),
    1
  );

  let (rsa_encrypt, rsa_decrypt) = rsa_key_gen(PRIME_2, PRIME_3);
  assert_eq!(rsa_encrypt.public_key.n, PRIME_2 * PRIME_3);
  assert_eq!(
    gcd(rsa_decrypt.private_key.d as u64, euler_totient(PRIME_2 as u64, PRIME_3 as u64)),
    1
  );

  let (rsa_encrypt, rsa_decrypt) = rsa_key_gen(PRIME_3, PRIME_1);
  assert_eq!(rsa_encrypt.public_key.n, PRIME_3 * PRIME_1);
  assert_eq!(
    gcd(rsa_decrypt.private_key.d as u64, euler_totient(PRIME_3 as u64, PRIME_1 as u64)),
    1
  );
}

#[test]
#[should_panic]
fn non_prime_key_gen() { rsa_key_gen(100, 200); }

#[test]
fn test_gcd() {
  assert_eq!(gcd(10, 5), 5);
  assert_eq!(gcd(10, 3), 1);
}

#[test]
fn test_generate_e() {
  let e = generate_e(PRIME_1, PRIME_2);
  assert_eq!(e, 3);

  let e = generate_e(PRIME_2, PRIME_3);
  assert_eq!(e, 5);

  let e = generate_e(PRIME_3, PRIME_1);
  assert_eq!(e, 5);
}

#[test]
fn test_mod_inverse() {
  assert_eq!(mod_inverse(3, 8), 3);
  assert_eq!(mod_inverse(5, 12), 5);
  assert_eq!(mod_inverse(5, 24), 5);
}

#[test]
fn test_encrypt_decrypt() {
  let message = 10;
  let (rsa_encrypt, rsa_decrypt) = rsa_key_gen(PRIME_1, PRIME_2);
  let cipher = rsa_encrypt.encrypt(message);
  let decrypted = rsa_decrypt.decrypt(cipher);
  assert_eq!(decrypted, message);

  let (rsa_encrypt, rsa_decrypt) = rsa_key_gen(PRIME_2, PRIME_3);
  let cipher = rsa_encrypt.encrypt(message);
  let decrypted = rsa_decrypt.decrypt(cipher);
  assert_eq!(decrypted, message);

  let message = 10;
  let (rsa_encrypt, rsa_decrypt) = rsa_key_gen(PRIME_3, PRIME_1);
  let cipher = rsa_encrypt.encrypt(message);
  let decrypted = rsa_decrypt.decrypt(cipher);
  assert_eq!(decrypted, message);

  let message = u16::MAX as u32;
  let (rsa_encrypt, rsa_decrypt) = rsa_key_gen(10007, 49999);
  let cipher = rsa_encrypt.encrypt(message);
  let decrypted = rsa_decrypt.decrypt(cipher);
  assert_eq!(decrypted, message);
}

#[test]
fn test_random_prime() {
  let prime = random_prime(1_000_000);
  assert!(is_prime(prime));
  assert!(prime >= 1_000_000);
}
