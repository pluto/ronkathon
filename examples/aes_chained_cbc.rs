//! Demonstrating AES chained CBC mode of operation where last ciphertext of previous operation is
//! used as IV for next operation. This has advantage as it reduces the bandwidth to share a new IV
//! each time between the parties. But in CBC mode, IV should be unpredictable, this was formalised in [CWE-329](https://cwe.mitre.org/data/definitions/329.html).
//!
//! But this scheme is not Chosen-Plaintext Attack secure and any
//! attacker can detect which original message was used in the ciphertext which is shown here.
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
use rand::{thread_rng, Rng};
use ronkathon::encryption::symmetric::{
  aes::{Block, Key, AES},
  modes::cbc::CBC,
};

fn attacker_chosen_message() -> [&'static [u8]; 2] {
  [b"You're gonna be pwned!", b"HAHA, You're gonna be dbl pwned!!"]
}

fn xor_blocks(a: &mut [u8], b: &[u8]) {
  for (x, y) in a.iter_mut().zip(b) {
    *x ^= *y;
  }
}

fn attacker<'a>(key: &Key<128>, iv: &Block, ciphertext: Vec<u8>) -> &'a [u8] {
  // Chose 2 random messages, {m_0, m_1}
  let messages = attacker_chosen_message();

  // first blocks' ciphertext
  let c1 = &ciphertext[..16];

  // select new IV as last blocks' ciphertext and initiate CBC with AES again with new IV
  let new_iv: [u8; 16] = ciphertext[ciphertext.len() - 16..].try_into().unwrap();
  let cbc2 = CBC::<AES<128>>::new(Block(new_iv));

  // Now, attacker selects the new message m_4 = IV ⨁ m_0 ⨁ NEW_IV
  let mut pwned_message = iv.0;
  xor_blocks(&mut pwned_message, messages[0]);
  xor_blocks(&mut pwned_message, &new_iv);

  // attacker receives ciphertext from encryption oracle
  let encrypted = cbc2.encrypt(key, &pwned_message);

  // attacker has gained knowledge about initial message
  if c1 == encrypted {
    messages[0]
  } else {
    messages[1]
  }
}

/// We simulate Chained CBC and show that attacker can know whether initial plaintext was message 1
/// or 2.
fn main() {
  let mut rng = thread_rng();

  // generate a random key and publicly known IV, and initiate CBC with AES cipher
  let key = Key::<128>::new(rng.gen());
  let iv = Block(rng.gen());
  let cbc = CBC::<AES<128>>::new(iv);

  // Chose 2 random messages, {m_0, m_1}
  let messages = attacker_chosen_message();

  // select a uniform bit b, and chose message m_b for encryption
  let bit = rng.gen_range(0..=1);
  let encrypted = cbc.encrypt(&key, messages[bit]);

  let predicted_message = attacker(&key, &iv, encrypted);

  assert_eq!(messages[bit], predicted_message);
}
