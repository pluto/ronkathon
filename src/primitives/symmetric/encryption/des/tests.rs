use rand::{thread_rng, Rng};

use super::*;

#[test]
fn des() {
  let mut rng = thread_rng();
  let secret_key = rng.gen();
  // let secret_key: u8 = 21;
  let des = Des::new(secret_key);
  println!("{:?}", des);
  // println!("{:b}", secret_key >> 2 & 1);
}
