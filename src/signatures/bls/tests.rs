
use super::*;

/// Creates a deterministic private key for testing using seed
fn create_test_private_key(seed: u64) -> BlsPrivateKey<PlutoBaseCurve> {
  BlsPrivateKey::generate_deterministic(seed)
}

#[test]
fn test_sign_and_verify() {
  let msg = b"Hello, BLS!";
  let sk = create_test_private_key(1234);
  let pk = sk.public_key();
  let sig = sk.sign::<PlutoExtendedCurve>(msg).expect("Signing should succeed");
  assert!(pk.verify(msg, &sig).is_ok(), "Valid signature should verify correctly");
}

#[test]
fn test_invalid_signature() {
  let msg = b"Hello, BLS!";
  let sk = create_test_private_key(1234);
  let pk = sk.public_key();
  let tampered_sig = BlsSignature { sig: AffinePoint::<PlutoExtendedCurve>::GENERATOR };
  assert!(pk.verify(msg, &tampered_sig).is_err(), "Tampered signature should fail verification");
}

#[test]
fn test_aggregate_signatures() {
  let msg = b"Hello, BLS!";
  let mut signatures = Vec::new();
  let mut public_keys = Vec::new();

  // Generate several keypairs with fixed seeds
  let test_seeds = [1234, 1234, 1234, 1234];
  for seed in test_seeds {
    let sk = create_test_private_key(seed);
    public_keys.push(sk.public_key());
    signatures.push(sk.sign::<PlutoExtendedCurve>(msg).expect("Signing should succeed"));
  }

  let aggregated_signature =
    BlsSignature::aggregate(&signatures).expect("Aggregation should succeed");

  assert!(
    verify_aggregated_signature_single_message::<PlutoBaseCurve, PlutoExtendedCurve>(
      &public_keys,
      msg,
      &aggregated_signature
    )
    .is_ok(),
    "Aggregated signature should verify correctly"
  );
}

#[test]
fn test_verify_aggregated_empty_public_keys() {
  let msg = b"Aggregate with Empty Public Keys";
  let sk = create_test_private_key(1111);
  let sig = sk.sign::<PlutoExtendedCurve>(msg).expect("Signing should succeed");

  let res = verify_aggregated_signature_single_message::<PlutoBaseCurve, PlutoExtendedCurve>(
    &[],
    &[],
    &sig,
  );
  assert!(res.is_err(), "Verification with empty public key list should fail");
}