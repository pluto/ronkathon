/// Example of Ed25519 digital signature algorithm.
use ronkathon::dsa::eddsa::Ed25519;

fn main() {
  let ed25519 = Ed25519::new(None);
  let msg = b"Hello World";

  let signature = ed25519.sign(msg);
  assert!(ed25519.verify(msg, signature));
}
