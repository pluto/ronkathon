/// Tiny RSA implementation
/// TinyRSA module for educational cryptographic implementations.

const PRIME_1: u32 = 5;
const PRIME_2: u32 = 3;

const fn field() -> u32 { PRIME_1 * PRIME_2 }

const fn euler_totient() -> u32 { (PRIME_1 - 1) * (PRIME_2 - 1) }

const fn gcd(a: u32, b: u32) -> u32 {
  if b == 0 {
    a
  } else {
    gcd(b, a % b)
  }
}

const fn generate_e() -> u32 {
  let totient = euler_totient();
  let mut e = 2;
  while e < totient {
    if gcd(totient, e) == 1 {
      return e;
    }
    e += 1;
  }
  0 // This should never happen if totient > 1
}

const fn mod_inverse(e: u32, totient: u32) -> u32 {
  let mut d = 1;
  while (d * e) % totient != 1 {
    d += 1;
  }
  d
}

fn encrypt(message: u32, e: u32) -> u32 { message.pow(e) % field() }

fn decrypt(cipher: u32, d: u32) -> u32 { cipher.pow(d) % field() }

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_field() {
    assert_eq!(field(), 15);
  }

  #[test]
  fn test_euler_totient() {
    assert_eq!(euler_totient(), 8);
  }

  #[test]
  fn test_gcd() {
    assert_eq!(gcd(10, 5), 5);
    assert_eq!(gcd(10, 3), 1);
  }

  #[test]
  fn test_generate_e() {
    assert_eq!(generate_e(), 3);
  }

  #[test]
  fn test_mod_inverse() {
    assert_eq!(mod_inverse(3, 8), 3);
  }

  #[test]
  fn test_encrypt_decrypt() {
    let message = 10;
    let e = generate_e();
    let d = mod_inverse(e, euler_totient());
    let cipher = encrypt(message, e);
    let decrypted = decrypt(cipher, d);
    assert_eq!(decrypted, message);
  }
}
