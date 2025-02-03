use ronkathon::{
  algebra::{field::prime::PlutoScalarField, group::FiniteCyclicGroup},
  curve::{pluto_curve::PlutoBaseCurve, AffinePoint},
  diffie_hellman::ecdh::compute_shared_secret,
};

const G: AffinePoint<PlutoBaseCurve> = AffinePoint::GENERATOR;

fn main() {
  let alice_secret = PlutoScalarField::new(420);
  let bob_secret = PlutoScalarField::new(69);

  let alice_public = G * alice_secret;
  let bob_public = G * bob_secret;

  let shared_secret_alice = compute_shared_secret(alice_secret, bob_public);
  let shared_secret_bob = compute_shared_secret(bob_secret, alice_public);

  assert_eq!(shared_secret_alice, shared_secret_bob);

  println!("Shared secret: {:#?}", shared_secret_alice);
}
