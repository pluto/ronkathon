//! BLS Signatures
//!
//! Implements Boneh–Lynn–Shacham (BLS) digital signatures using ronkathon's
//! existing curve and pairing primitives. This module demonstrates key generation,
//! signing, verification, and aggregation (for signatures on the same message).
//!
use rand::Rng;

use crate::{
  algebra::{
    field::{extension::GaloisField, prime::PlutoScalarField, Field},
    group::FiniteCyclicGroup,
    Finite,
  },
  curve::{self, pairing::pairing, pluto_curve::PlutoExtendedCurve, AffinePoint},
  hashes::sha3::Sha3_256 as Sha256,
};

/// Errors that can occur during BLS signature operations.
#[derive(Debug)]
pub enum BlsError {
  /// The provided public key is invalid.
  InvalidPublicKey,
  /// The signature is invalid.
  InvalidSignature,
  /// Hash-to-curve failed to find a valid point on the curve.
  HashToCurveFailed,
  /// Signature verification failed.
  VerificationFailed,
  /// Other error with a descriptive message.
  Other(String),
}

/// BLS private key.
pub struct BlsPrivateKey {
  sk: PlutoScalarField,
}

/// BLS public key.
pub struct BlsPublicKey {
  pk: AffinePoint<PlutoExtendedCurve>,
}

/// BLS signature.
pub struct BlsSignature {
  sig: AffinePoint<PlutoExtendedCurve>,
}

impl BlsPrivateKey {
  /// Generates a new BLS private key using the provided random number generator.
  pub fn generate<R: Rng>(rng: &mut R) -> Self {
    // Generate a random scalar in the range [1, ORDER]
    let sk = PlutoScalarField::new(rng.gen_range(1..=PlutoScalarField::ORDER));
    BlsPrivateKey { sk }
  }

  /// Returns the corresponding BLS public key.
  pub fn public_key(&self) -> BlsPublicKey {
    // Calculate public key as sk * G, where G is the generator of the subgroup.
    let pk = AffinePoint::<PlutoExtendedCurve>::GENERATOR * self.sk;
    BlsPublicKey { pk }
  }

  /// Signs a message using the BLS private key.
  ///
  /// The signature is computed as sk * H(m), where H is a hash-to-curve function.
  pub fn sign(&self, msg: &[u8]) -> Result<BlsSignature, BlsError> {
    let hash_point = hash_to_curve(msg)?;
    let sig_point = hash_point * self.sk;
    Ok(BlsSignature { sig: sig_point })
  }
}

impl BlsPublicKey {
  /// Verifies a BLS signature against the given message.
  ///
  /// The verification check uses the bilinear pairing:
  ///   e(signature, G) == e(H(message), public_key)
  pub fn verify(&self, msg: &[u8], signature: &BlsSignature) -> Result<(), BlsError> {
    let hash_point = hash_to_curve(msg)?;
    let left = pairing::<PlutoExtendedCurve, 17>(
      signature.sig,
      AffinePoint::<PlutoExtendedCurve>::GENERATOR,
    );
    let right = pairing::<PlutoExtendedCurve, 17>(hash_point, self.pk);
    if left == right {
      Ok(())
    } else {
      Err(BlsError::VerificationFailed)
    }
  }
}

impl BlsSignature {
  /// Aggregates multiple BLS signatures into a single signature.
  ///
  /// This function sums the individual signature points. All signatures must be on the same
  /// message.
  pub fn aggregate(signatures: &[BlsSignature]) -> Result<BlsSignature, BlsError> {
    if signatures.is_empty() {
      return Err(BlsError::Other("No signatures to aggregate".into()));
    }
    let mut agg = signatures[0].sig;
    for sig in signatures.iter().skip(1) {
      agg += sig.sig;
    }
    Ok(BlsSignature { sig: agg })
  }
}

/// Verifies an aggregated BLS signature for a single common message.
///
/// For aggregated signatures the verification check is:
///   e(aggregated_signature, G) == e(H(message), ∑ public_keys)
pub fn verify_aggregated_signature(
  msg: &[u8],
  pks: &[BlsPublicKey],
  aggregated_sig: &BlsSignature,
) -> Result<(), BlsError> {
  if pks.is_empty() {
    return Err(BlsError::Other("No public keys provided".into()));
  }
  let mut agg_pk = pks[0].pk;
  for pk in pks.iter().skip(1) {
    agg_pk += pk.pk;
  }
  let hash_point = hash_to_curve(msg)?;
  let left = pairing::<PlutoExtendedCurve, 17>(
    aggregated_sig.sig,
    AffinePoint::<PlutoExtendedCurve>::GENERATOR,
  );
  let right = pairing::<PlutoExtendedCurve, 17>(hash_point, agg_pk);
  if left == right {
    Ok(())
  } else {
    Err(BlsError::VerificationFailed)
  }
}

/// Add this helper function 
fn canonicalize<F>(x: F) -> F 
where
    F: Field + Clone + std::ops::Neg<Output = F> + PartialOrd
{
    let neg = -x.clone();
    // Compare the first coefficient of the field element
    if x > neg {
        neg
    } else {
        x
    }
}

/// Converts a message to a point on the curve using a basic try-and-increment hash-to-curve method.
///
fn hash_to_curve(msg: &[u8]) -> Result<AffinePoint<PlutoExtendedCurve>, BlsError> {
  let mut counter = 0u32;
  loop {
    let mut hasher = Sha256::new();
    hasher.update(msg);
    hasher.update(&counter.to_be_bytes());
    let hash_result = hasher.finalize();
    if hash_result.len() < 8 {
      return Err(BlsError::Other("Hash output too short".into()));
    }
    let x_bytes: [u8; 8] = hash_result[0..8].try_into().unwrap();
    let x_val = u64::from_be_bytes(x_bytes);
    
    let candidate_x = 
        <PlutoExtendedCurve as curve::EllipticCurve>::BaseField::from(x_val);
    
    let x3 = candidate_x * candidate_x * candidate_x;
    let y2 = x3 + <PlutoExtendedCurve as curve::EllipticCurve>::BaseField::from(3u64);
    
    if let Some(sqrt_result) = y2.sqrt() {
        let candidate_y = canonicalize(sqrt_result.0);
        let point = AffinePoint::<PlutoExtendedCurve>::new(candidate_x, candidate_y);
        
        // Make sure the point is in the correct subgroup
        let subgroup_order = 17;
        if (point * PlutoScalarField::new(subgroup_order)) 
            == AffinePoint::<PlutoExtendedCurve>::Infinity
        {
            // Check that the point isn't the identity element
            if point != AffinePoint::<PlutoExtendedCurve>::Infinity {
                return Ok(point);
            }
        }
    }
    counter += 1;
    if counter > 1000 {
        return Err(BlsError::HashToCurveFailed);
    }
  }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::thread_rng;

    /// Test that a valid signature verifies correctly.
    #[test]
    fn test_sign_and_verify() {
        let msg = b"Hello, BLS!";
        let mut rng = thread_rng();
        let sk = BlsPrivateKey::generate(&mut rng);
        let pk = sk.public_key();
        let sig = sk.sign(msg).expect("Signing should succeed");
       
        assert!(
            pk.verify(msg, &sig).is_ok(),
            "Valid signature should verify correctly"
        );
    }

    /// Test that the signature for an empty message verifies correctly.
    #[test]
    fn test_empty_message() {
        let msg = b"";
        let mut rng = thread_rng();
        let sk = BlsPrivateKey::generate(&mut rng);
        let pk = sk.public_key();
        let sig = sk.sign(msg).expect("Signing an empty message should succeed");
        assert!(
            pk.verify(msg, &sig).is_ok(),
            "Signature for an empty message should verify correctly"
        );
    }

    /// Test that tampering with a valid signature causes verification to fail.
    #[test]
    fn test_invalid_signature() {
        let msg = b"Test message";
        let mut rng = thread_rng();
        let sk = BlsPrivateKey::generate(&mut rng);
        let pk = sk.public_key();
        // Create a valid signature.
        let sig = sk.sign(msg).expect("Signing should succeed");
        // Tamper with the signature by adding the generator point.
        let tampered_sig = BlsSignature {
            sig: sig.sig + AffinePoint::<PlutoExtendedCurve>::GENERATOR,
        };
        assert!(
            pk.verify(msg, &tampered_sig).is_err(),
            "Tampered signature should fail verification"
        );
    }

    /// Test that aggregating multiple signatures on the same message verifies correctly.
    #[test]
    fn test_aggregate_signatures() {
        let msg = b"Aggregate Test Message";
        let mut rng = thread_rng();

        let mut signatures = Vec::new();
        let mut public_keys = Vec::new();

        // Generate several keypairs and corresponding signatures.
        for _ in 0..4 {
            let sk = BlsPrivateKey::generate(&mut rng);
            public_keys.push(sk.public_key());
            signatures.push(sk.sign(msg).expect("Signing should succeed"));
        }

        // Aggregate the signatures and verify the aggregated signature.
        let aggregated_signature =
            BlsSignature::aggregate(&signatures).expect("Aggregation should succeed");
        assert!(
            verify_aggregated_signature(msg, &public_keys, &aggregated_signature).is_ok(),
            "Aggregated signature should verify correctly"
        );
    }

    /// Test that trying to aggregate an empty slice of signatures produces an error.
    #[test]
    fn test_aggregate_empty_signatures() {
        let res = BlsSignature::aggregate(&[]);
        assert!(
            res.is_err(),
            "Aggregating an empty signature list should return an error"
        );
    }

    /// Test that verifying an aggregated signature with an empty public key list fails.
    #[test]
    fn test_verify_aggregated_empty_public_keys() {
        let msg = b"Aggregate with Empty Public Keys";
        let mut rng = thread_rng();
        let sk = BlsPrivateKey::generate(&mut rng);
        let sig = sk.sign(msg).expect("Signing should succeed");
        let res = verify_aggregated_signature(msg, &[], &sig);
        assert!(
            res.is_err(),
            "Verification with an empty public key list should fail"
        );
    }
}
