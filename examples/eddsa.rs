use ronkathon::dsa::eddsa::Ed25519;

fn main() {
  let (sk, pk) = Ed25519::keygen(None);
  let msg = b"Hello World";

  let signature = Ed25519::sign(sk, pk, msg);
  assert!(Ed25519::verify(pk, msg, signature));
}
