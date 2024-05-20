use super::*;
const PRIME_1: usize = 5;
const PRIME_2: usize = 3;

#[test]
fn test_euler_totient() {
  assert_eq!(euler_totient(PRIME_1 as u64, PRIME_2 as u64), 8);
}

#[test]
fn test_gcd() {
  assert_eq!(gcd(10, 5), 5);
  assert_eq!(gcd(10, 3), 1);
}

#[test]
fn test_generate_e() {
  let e = generate_e(PRIME_1, PRIME_2);
  assert_eq!(e, 3);
}

#[test]
fn test_mod_inverse() {
  assert_eq!(mod_inverse(3, 8), 3);
}

#[test]
fn test_encrypt_decrypt() {
  let message = 10;
  let key = rsa_key_gen();
  let cipher = key.encrypt(message);
  let decrypted = key.decrypt(cipher);
  assert_eq!(decrypted, message);
}

#[test]
fn test_random_prime() {
  let prime = random_prime(2);
  assert!(is_prime(prime));
  assert!(prime >= 1_000_000);
}

#[test]
fn test_random_prime_generation() {
  let prime = random_prime(2);
  assert!(is_prime(prime));
  assert!(prime >= 1_000_000);
}
