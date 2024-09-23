//! This code example demonstrates the key feature of GCM cipher mode over CTR mode, which is
//! authentication.

#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use std::{fmt::Write, str};

use rand::{thread_rng, Rng};
use ronkathon::encryption::symmetric::{
  aes::{Key, AES},
  modes::gcm::GCM,
};

/// Encode bytes to hex
pub fn encode_hex(bytes: &[u8]) -> String {
  let mut s = String::with_capacity(bytes.len() * 2);
  for &b in bytes {
    write!(&mut s, "{:02x}", b).unwrap();
  }
  s
}

fn ideal_world(msg: &[u8]){
  println!("---Ideal World!---\n");

  let mut rng = thread_rng();
  let key = Key::<128>::new(rng.gen());
  let iv: [u8; 12] = rng.gen();
  let gcm = GCM::<AES<128>>::new(key);

  let (enc, tag1) = gcm.encrypt(&iv, msg, b"").unwrap();

  println!("msg:\t{}(={})", encode_hex(msg), str::from_utf8(msg).unwrap());

  println!("enc:\t{}", encode_hex(&enc));

  println!("tag1:\t{}", encode_hex(&tag1));

  let (dec, tag2) = gcm.decrypt(&iv, &enc, b"").unwrap();
  println!("dec:\t{}(={})", encode_hex(&dec), str::from_utf8(&dec).unwrap());

  assert_eq!(tag1, tag2);

  println!("tag2:\t{}", encode_hex(&tag2));
}
fn real_world(msg: &[u8]) {
  println!("\n---Real World!---\n");

  let mut rng = thread_rng();
  let key = Key::<128>::new(rng.gen());
  let iv: [u8; 12] = rng.gen();
  let gcm = GCM::<AES<128>>::new(key);

  let (mut enc, tag1) = gcm.encrypt(&iv, msg, b"").unwrap();

  println!("msg:\t{}(={})", encode_hex(msg), str::from_utf8(msg).unwrap());

  println!("enc:\t{}", encode_hex(&enc));
  println!("enc_tag:{}", encode_hex(&tag1));

  enc[3] += 1;
  enc[4] += 1;
  enc[6] += 1;

  println!("bad enc:{}", encode_hex(&enc));

  let (dec, tag2) = gcm.decrypt(&iv, &enc, b"").unwrap();
  println!("dec:\t{}(={})", encode_hex(&dec), str::from_utf8(&dec).unwrap());
  println!("dec_tag:{}", encode_hex(&tag2)); 

  assert!(tag1 != tag2);
  println!("The tags are not equal!");
}

fn main(){
    let message = b"Hello World!";

    ideal_world(message);

    real_world(message);
}
