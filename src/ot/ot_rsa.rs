//! Contains implementation of 1-out-of-2 OT using RSA encryption.

use rand::{thread_rng, Rng};

use crate::encryption::asymmetric::rsa::{rsa_key_gen, RSADecryption, RSAEncryption};

/// Sender that has two messages and wants to send one of it to [`OTReceiver`] without knowledge of
/// which one.
pub struct OTSender {
  messages:        [usize; 2],
  random_messages: [usize; 2],
  rsa_decrypt:     RSADecryption,
}

/// Receiver wants to get access to one of the message that [`OTSender`] has without knowledge of
/// the other.
pub struct OTReceiver {
  choice: bool,
  key:    usize,
}

impl OTSender {
  /// create a new [`OTSender`] object.
  /// ## Arguments
  /// - `messages`: message that sender has access to
  /// - `primes`: [`RSAEncryption`] primes
  pub fn new(messages: [usize; 2], primes: [usize; 2]) -> (Self, RSAEncryption, [usize; 2]) {
    let (rsa_encrypt, rsa_decrypt) = rsa_key_gen(primes[0], primes[1]);

    let random_messages: [usize; 2] = rand::random();
    (OTSender { messages, rsa_decrypt, random_messages }, rsa_encrypt, random_messages)
  }

  /// Encrypt messages with receiver's choice
  pub fn encrypt(&self, v: usize) -> [usize; 2] {
    let k0 = if v < self.random_messages[0] {
      v + self.rsa_decrypt.private_key.n
        - (self.random_messages[0] % self.rsa_decrypt.private_key.n)
    } else {
      v - self.random_messages[0]
    };
    let k1 = if v < self.random_messages[1] {
      v + self.rsa_decrypt.private_key.n
        - (self.random_messages[1] % self.rsa_decrypt.private_key.n)
    } else {
      v - self.random_messages[1]
    };

    let k0 = self.rsa_decrypt.decrypt((k0) as u32);
    let k1 = self.rsa_decrypt.decrypt((k1) as u32);

    println!("k0: {}, k1: {}", k0, k1);

    let m0 = (self.messages[0] + k0 as usize) % self.rsa_decrypt.private_key.n;
    let m1 = (self.messages[1] + k1 as usize) % self.rsa_decrypt.private_key.n;

    [m0, m1]
  }
}

impl OTReceiver {
  /// create new [`OTReceiver`] object
  /// ## Arguments
  /// - `choice`: receiver message choice
  pub fn new(choice: bool) -> Self {
    let mut rng = thread_rng();
    Self { choice, key: rng.gen::<u32>() as usize }
  }

  /// Encrypts receiver's choice out of sender's messages.
  ///
  /// v = (x_b + k^e) mod N
  pub fn encrypt(&self, rsa_encrypt: RSAEncryption, sender_messages: [usize; 2]) -> usize {
    println!("key: {}", self.key % rsa_encrypt.public_key.n);
    (rsa_encrypt.encrypt(self.key as u32) as usize + sender_messages[self.choice as usize])
      % rsa_encrypt.public_key.n
  }

  /// Decrypts sender's encrypted message
  ///
  /// m_b = (m'_b - k) mod N
  /// ## Arguments:
  /// - `messages`: sender's encrypted messages: m'_0, m'_1
  /// - `modulus`: RSA modulus
  pub fn decrypt(&self, messages: [usize; 2], modulus: usize) -> usize {
    if messages[self.choice as usize] < self.key {
      (messages[self.choice as usize] + modulus - (self.key % modulus)) % modulus
    } else {
      (messages[self.choice as usize] - self.key) % modulus
    }
  }
}

#[cfg(test)]
mod tests {

  use super::*;

  #[test]
  fn ot_rsa() {
    let mut rng = thread_rng();
    let messages = [10, 2];
    let random_primes = [19, 13];

    let (ot_sender, rsa_encrypt, random_messages) = OTSender::new(messages, random_primes);

    let modulus = rsa_encrypt.public_key.n;

    let bit = rng.gen::<bool>();
    let ot_receiver = OTReceiver::new(bit);

    let v = ot_receiver.encrypt(rsa_encrypt, random_messages);

    let encrypted_messages = ot_sender.encrypt(v);

    let message = ot_receiver.decrypt(encrypted_messages, modulus);

    assert_eq!(message, messages[bit as usize]);
  }
}
