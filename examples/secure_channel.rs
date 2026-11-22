//! Alice and Bob set up an encrypted and authenticated channel by chaining four primitives:
//!
//! 1. ECDH on the Pluto curve to agree on a shared point.
//! 2. HMAC-SHA256 as a key derivation function, to turn that point into separate encryption and MAC
//!    keys.
//! 3. ChaCha20 to encrypt the message.
//! 4. HMAC-SHA256 over the nonce and ciphertext (encrypt-then-MAC), so Bob can tell if anything was
//!    changed on the way.
//!
//! Run it with your own message: `cargo run --example secure_channel -- "meet me at noon"`.
//!
//! **Note**: the Pluto curve's subgroup only has 17 elements, so the shared secret can be guessed
//! and none of this is secure. It shows how the pieces fit together.
use rand::{thread_rng, Rng};
use ronkathon::{
  algebra::{field::prime::PlutoScalarField, group::FiniteCyclicGroup},
  curve::{pluto_curve::PlutoBaseCurve, AffinePoint},
  diffie_hellman::ecdh::compute_shared_secret,
  encryption::symmetric::chacha::{Counter, IETFChaCha20},
  hmac::hmac_sha256::hmac_sha256,
};

const G: AffinePoint<PlutoBaseCurve> = AffinePoint::GENERATOR;

/// Prints a point as `(x, y)`.
fn show(point: AffinePoint<PlutoBaseCurve>) -> String {
  match point {
    AffinePoint::Point(x, y) => format!("({x}, {y})"),
    AffinePoint::Infinity => "the point at infinity".to_string(),
  }
}

/// The keys both parties derive from the shared point.
struct SessionKeys {
  encryption: [u32; 8],
  mac:        [u8; 32],
}

/// Derives an encryption key and a MAC key from the ECDH shared point, using HMAC-SHA256 with the
/// point as key and a different label for each derived key.
fn derive_keys(shared: AffinePoint<PlutoBaseCurve>) -> SessionKeys {
  let AffinePoint::Point(x, y) = shared else { panic!("shared secret is the point at infinity") };
  let secret =
    [(Into::<usize>::into(x) as u64).to_be_bytes(), (Into::<usize>::into(y) as u64).to_be_bytes()]
      .concat();

  let encryption_bytes = hmac_sha256(&secret, b"secure_channel encryption key");
  let mut encryption = [0_u32; 8];
  for (word, bytes) in encryption.iter_mut().zip(encryption_bytes.chunks(4)) {
    *word = u32::from_le_bytes(bytes.try_into().unwrap());
  }

  SessionKeys { encryption, mac: hmac_sha256(&secret, b"secure_channel mac key") }
}

/// The MAC covers the nonce and the ciphertext.
fn tag(keys: &SessionKeys, nonce: &[u32; 3], ciphertext: &[u8]) -> [u8; 32] {
  let nonce_bytes: Vec<u8> = nonce.iter().flat_map(|word| word.to_le_bytes()).collect();
  hmac_sha256(&keys.mac, &[nonce_bytes.as_slice(), ciphertext].concat())
}

/// Compares two tags without returning early, so the time taken doesn't depend on where they
/// differ.
fn tags_equal(a: &[u8; 32], b: &[u8; 32]) -> bool {
  a.iter().zip(b).fold(0_u8, |diff, (x, y)| diff | (x ^ y)) == 0
}

/// What Bob does with a message from Alice: check the tag first, and only decrypt if it matches.
fn receive(
  keys: &SessionKeys,
  nonce: &[u32; 3],
  ciphertext: &[u8],
  received_tag: &[u8; 32],
) -> Option<Vec<u8>> {
  if !tags_equal(&tag(keys, nonce, ciphertext), received_tag) {
    return None;
  }
  let chacha = IETFChaCha20::new(&keys.encryption, nonce);
  Some(chacha.decrypt(&Counter::new([1]), ciphertext).unwrap())
}

fn main() {
  let message = std::env::args().skip(1).collect::<Vec<_>>().join(" ");
  let message = if message.is_empty() { "meet me at noon".to_string() } else { message };
  let mut rng = thread_rng();

  println!("1. Key exchange (ECDH)");
  // a secret of 0 would give the point at infinity as public key
  let alice_secret = PlutoScalarField::new(rng.gen_range(1..17));
  let bob_secret = PlutoScalarField::new(rng.gen_range(1..17));
  let alice_public = G * alice_secret;
  let bob_public = G * bob_secret;
  println!("   Alice publishes {}", show(alice_public));
  println!("   Bob publishes   {}", show(bob_public));

  let alice_shared = compute_shared_secret(alice_secret, bob_public);
  let bob_shared = compute_shared_secret(bob_secret, alice_public);
  assert_eq!(alice_shared, bob_shared);
  println!("   both compute    {}", show(alice_shared));

  println!("\n2. Key derivation (HMAC-SHA256)");
  let alice_keys = derive_keys(alice_shared);
  let bob_keys = derive_keys(bob_shared);
  println!("   MAC key: {}", hex::encode(alice_keys.mac));

  println!("\n3. Alice encrypts (ChaCha20) and authenticates (HMAC-SHA256)");
  let nonce: [u32; 3] = rng.gen();
  let chacha = IETFChaCha20::new(&alice_keys.encryption, &nonce);
  let ciphertext = chacha.encrypt(&Counter::new([1]), message.as_bytes()).unwrap();
  let alice_tag = tag(&alice_keys, &nonce, &ciphertext);
  println!("   message:    {message:?}");
  println!("   ciphertext: {}", hex::encode(&ciphertext));
  println!("   tag:        {}", hex::encode(alice_tag));

  println!("\n4. Bob checks the tag and decrypts");
  let received = receive(&bob_keys, &nonce, &ciphertext, &alice_tag).expect("tag should match");
  let received = String::from_utf8(received).unwrap();
  println!("   Bob reads {received:?}");
  assert_eq!(received, message);

  println!("\n5. Someone flips a bit of the ciphertext on the way");
  let mut tampered = ciphertext.clone();
  tampered[0] ^= 1;
  match receive(&bob_keys, &nonce, &tampered, &alice_tag) {
    Some(_) => panic!("a tampered ciphertext must not be accepted"),
    None => println!("   Bob rejects it: the tag doesn't match"),
  }
}
