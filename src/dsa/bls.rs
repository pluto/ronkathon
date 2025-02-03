use crypto_bigint::U256;
use crate::algebra::field::prime::PrimeField;
use crate::algebra::field::Field;
use crate::algebra::group::FiniteCyclicGroup;
use crate::dsa::utils::{hkdf_extract, hkdf_expand, i2osp, os2ip};
use crate::{algebra::field::prime::{PlutoScalarField, PlutoBaseField}, PlutoBaseFieldExtension, curve::{AffinePoint, EllipticCurve,pluto_curve::{
     PlutoBaseCurve, PlutoExtendedCurve,
}}};
use crate::curve::pairing::pairing;
use crate::hashes::sha::Sha256;

/// Computes the SHA-256 digest of the input data.
fn hash(data: &[u8]) -> Vec<u8> {
    let hasher = Sha256::new();
    hasher.digest(data)
    
}

/// Given a message, returns a point in the extended group.
/// Note: This is a _dummy_ (insecure) hash-to-curve implementation. In production you would
/// use a standard method (e.g. hash-to-curve with a suite such as "SvdW" or "Elligator2").
fn hash_to_point(message: &[u8]) -> AffinePoint<PlutoExtendedCurve> {
    let digest = hash(message);
    // Use (a portion of) the hash to produce dummy field elements.
    // Here we use the first 16 octets to compute two values.
    let x_val = u64::from_be_bytes(digest[0..8].try_into().unwrap());
    let y_val = u64::from_be_bytes(digest[8..16].try_into().unwrap());
    let x = PlutoBaseFieldExtension::new([PlutoBaseField::new(x_val as usize), PlutoBaseField::new(0)]);
    let y = PlutoBaseFieldExtension::new([PlutoBaseField::new(y_val as usize), PlutoBaseField::new(0)]);
    AffinePoint::<PlutoExtendedCurve>::new(x, y)
}

/// Converts an octet string (assumed to be 48 octets) to a public key point on the base curve.
/// Returns `None` if the length is incorrect.
pub fn pubkey_to_point(pubkey: &[u8]) -> Option<AffinePoint<PlutoBaseCurve>> {
    if pubkey.len() != 48 {
        return None;
    }
    let x_val = u64::from_be_bytes(pubkey[0..24].try_into().unwrap());
    let y_val = u64::from_be_bytes(pubkey[24..48].try_into().unwrap());
    let x = PrimeField::new(x_val as usize);
    let y = PrimeField::new(y_val as usize);
    Some(AffinePoint::<PlutoBaseCurve>::new(x,y))
}

/// Converts an octet string (assumed to be 48 octets) to a signature point on the extended curve.
pub fn signature_to_point(sig: &[u8]) -> Option<AffinePoint<PlutoExtendedCurve>> {
    if sig.len() != 48 {
        return None;
    }
    let x_val = u64::from_be_bytes(sig[0..24].try_into().unwrap());
    let y_val = u64::from_be_bytes(sig[24..48].try_into().unwrap());
    let x = PlutoBaseFieldExtension::new([PlutoBaseField::new(x_val as usize), PlutoBaseField::new(0)]);
    let y = PlutoBaseFieldExtension::new([PlutoBaseField::new(y_val as usize), PlutoBaseField::new(0)]);
    Some(AffinePoint::<PlutoExtendedCurve>::new(x,y))
}

/// Returns the identity element of GT (i.e. 1 in the target group).
fn gt_identity() -> <PlutoExtendedCurve as crate::curve::EllipticCurve>::BaseField {
   PlutoBaseFieldExtension::ONE
}

/// Returns the product of two GT elements.
fn gt_mul(
    a: <PlutoExtendedCurve as crate::curve::EllipticCurve>::BaseField,
    b: <PlutoExtendedCurve as crate::curve::EllipticCurve>::BaseField,
) -> <PlutoExtendedCurve as crate::curve::EllipticCurve>::BaseField {
    a * b
}

/// KeyGen: Deterministically derives a nonzero secret key (an element of PlutoScalarField)
/// from a secret octet string IKM using HKDF.
///
/// The algorithm is as follows:
///
/// 1. Loop:
///    a. PRK = HKDF-Extract(salt, IKM || I2OSP(0,1))
///    b. Let L = ceil((3*ceil(log₂(r)))/16) where r is the subgroup order.
///    c. OKM = HKDF-Expand(PRK, (key_info || I2OSP(L,2)), L)
///    d. Let candidate = OS2IP(OKM) mod r.
///    e. If candidate ≠ 0, convert candidate to a PlutoScalarField and return it.
///    f. Otherwise, set salt = H(salt) and repeat.
pub fn keygen(
    ikm: &[u8],
    salt: &[u8],
    key_info: Option<&[u8]>,
) -> Result<PlutoScalarField, String> {
    let key_info = key_info.unwrap_or(&[]);
    let mut ikm_prime = ikm.to_vec();
    // Append I2OSP(0, 1) – a one-octet string representing zero.
    let zero_ospi = i2osp(&U256::ZERO, 1)?;
    ikm_prime.extend_from_slice(&zero_ospi);
    let mut salt_current = salt.to_vec();

    // Use the order r from the base curve.
    let r_uint = crypto_bigint::NonZero::new(U256::from(PlutoBaseCurve::ORDER as u64)).unwrap();
    let r_bits = (PlutoBaseCurve::ORDER as f64).log2().ceil() as usize;
    let L = (3 * r_bits + 15) / 16; // ceil((3 * r_bits) / 16)

    loop {
        let prk = hkdf_extract(&salt_current, &ikm_prime);
        let mut info = key_info.to_vec();
        let L_ospi = i2osp(&U256::from(L as u64), 2)?;
        info.extend_from_slice(&L_ospi);
        let okm = hkdf_expand(&prk, &info, L);
        let candidate_uint = os2ip(&okm)?;
        let sk_uint = candidate_uint.rem(&r_uint);
        if sk_uint != U256::ZERO {
            // Convert candidate (of type U256) into PlutoScalarField.
            // We assume an associated method `from_uint` exists.
            return Ok(PlutoScalarField::new(sk_uint.bits() as usize));
        }
        salt_current = hash(&salt_current);
    }
}

/// SkToPk: Computes the public key from a secret key by performing scalar multiplication
/// on the base curve’s generator.
pub fn sk_to_pk(sk: &PlutoScalarField) -> Vec<u8> {
    let g: AffinePoint<PlutoBaseCurve> = AffinePoint::<PlutoBaseCurve>::GENERATOR;
    // Compute pk = sk * G.
    let pk_point = g * *sk;
   if let AffinePoint::Point(x,y ) = pk_point {
     return [x.value.to_be_bytes(),y.value.to_be_bytes()].concat().to_vec();
   }else {
    return vec![0]
   }
}

/// Sign: Computes a deterministic signature over `message` using secret key `sk`.
///
/// The procedure is:
///    1. Q = hash_to_point(message) in the extended group (G₂).
///    2. signature = sk * Q.
pub fn sign(sk: &PlutoScalarField, message: &[u8]) -> Vec<u8> {
    let q = hash_to_point(message);
    let signature_point = q * *sk;
    if let AffinePoint::Point(x,y ) = signature_point {
        return [x.coeffs[0].value.to_be_bytes(),y.coeffs[0].value.to_be_bytes()].concat().to_vec();
      }else {
       return vec![0]
      }
    }
/// Verify: Checks that `signature` is a valid signature on `message` under public key `pk`.
///
/// This implementation converts the base–curve public key into the extended curve so that
/// the pairing can be applied. Verification uses the equation:
///
///  e(PK_ext, Q) = e(G_ext, signature)
///
/// where Q = hash_to_point(message) and the _G_ext_ view of the base–curve generator is computed
/// via the `From<AffinePoint<PlutoBaseCurve>> for AffinePoint<PlutoExtendedCurve>` conversion.
pub fn verify(pk: &[u8], message: &[u8], signature: &[u8]) -> bool {
    // Parse the public key as a point on the base curve.
    let pk_point = match pubkey_to_point(pk) {
        Some(pt) => pt,
        None => return false,
    };
    // Convert the public key to the extended group.
    let pk_ext: AffinePoint<PlutoExtendedCurve> = pk_point.into();
    // Parse the signature as a point on the extended curve.
    let sig_point = match signature_to_point(signature) {
        Some(pt) => pt,
        None => return false,
    };
    let q = hash_to_point(message);
    // Convert the base generator into the extended group.
    let g_base = AffinePoint::<PlutoBaseCurve>::GENERATOR;
    let g_ext: AffinePoint<PlutoExtendedCurve> = g_base.into();
    // Compute pairings (using an R loop parameter of 17, per our test environment).
    let c1 = pairing::<PlutoExtendedCurve, 17>(pk_ext, q);
    let c2 = pairing::<PlutoExtendedCurve, 17>(g_ext, sig_point);
    c1 == c2
}

/// Aggregate: Aggregates a set of signatures (each a serialized affine point on the extended curve)
/// into one aggregated signature (by point‐addition).
pub fn aggregate(signatures: &[&[u8]]) -> Result<Vec<u8>, String> {
    if signatures.is_empty() {
        return Err("No signatures provided".to_string());
    }
    let mut agg_point = signature_to_point(signatures[0])
        .ok_or_else(|| "Invalid signature".to_string())?;
    for &sig in signatures.iter().skip(1) {
        let pt = signature_to_point(sig)
            .ok_or_else(|| "Invalid signature in aggregation".to_string())?;
        agg_point += pt;
    }
    if let AffinePoint::Point(x,y ) = agg_point{
        Ok([x.coeffs[0].value.to_be_bytes(),y.coeffs[0].value.to_be_bytes()].concat().to_vec())
      }else {
       Ok(vec![0])
      }
    
}

/// AggregateVerify: Verifies that an aggregated signature is valid for the provided set of
/// (public key, message) pairs.
///
/// For each public key (serialized on the base curve), we convert it to the extended curve;
/// we then hash the corresponding message into a point (in the extended group) and multiply together
/// the pairing values. The verification accepts if:
///
///  ∏[i] e(convert(pkᵢ), H(messageᵢ)) = e(convert(G), aggregated_signature)
pub fn aggregate_verify(pks: &[&[u8]], messages: &[&[u8]], agg_signature: &[u8]) -> bool {
    if pks.is_empty() || messages.is_empty() || pks.len() != messages.len() {
        return false;
    }
    let agg_point = match signature_to_point(agg_signature) {
        Some(pt) => pt,
        None => return false,
    };
    
    let mut prod = gt_identity();
    for (pk_bytes, msg) in pks.iter().zip(messages.iter()) {
        let pk_point = match pubkey_to_point(pk_bytes) {
            Some(pt) => pt,
            None => return false,
        };
        // (Optional) Ensure that the public key passes validation.
        if !key_validate(pk_bytes) {
            return false;
        }
        let pk_ext: AffinePoint<PlutoExtendedCurve> = pk_point.into();
        let q = hash_to_point(msg);
        let pairing_val = pairing::<PlutoExtendedCurve, 17>(pk_ext, q);
        prod = gt_mul(prod, pairing_val);
    }
    let g_base = AffinePoint::<PlutoBaseCurve>::GENERATOR;
    let g_ext: AffinePoint<PlutoExtendedCurve> = g_base.into();
    let c2 = pairing::<PlutoExtendedCurve, 17>(g_ext, agg_point);
    prod == c2
}

/// KeyValidate: Returns true if the provided public key (serialized) represents a valid point
/// on the base curve and is nonzero. Here we also do a (dummy) subgroup check by verifying that
/// multiplying the point by the group order yields the point at infinity.
pub fn key_validate(pk: &[u8]) -> bool {
    if let Some(point) = pubkey_to_point(pk) {
        if point== AffinePoint::Infinity {
            return false;
        }
        // For a proper subgroup check, one would verify (point * ORDER) == Infinity.
        (point * PlutoScalarField::new(PlutoBaseCurve::ORDER)) == AffinePoint::Infinity
    } else {
        false
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crypto_bigint::U256;

    #[test]
    fn test_keygen_and_sk_to_pk() {
        let ikm = b"this is a secret key material with enough bytes........";
        let salt = b"BLS-SIG-KEYGEN-SALT-"; // 20 octets if ASCII
        let sk = keygen(ikm, salt, None).unwrap();
        assert!(sk != PrimeField::new(0));
        let pk = sk_to_pk(&sk);
        assert_eq!(pk.len(), 48);
    }

    #[test]
    fn test_sign_and_verify() {
        let ikm = b"another secret key material with sufficient entropy........";
        let salt = b"BLS-SIG-KEYGEN-SALT-";
        let sk = keygen(ikm, salt, None).unwrap();
        let pk = sk_to_pk(&sk);
        let message = b"Test message for signing";
        let signature = sign(&sk, message);
        assert!(verify(&pk, message, &signature));
        // A tampered message should not verify.
        assert!(!verify(&pk, b"Another message", &signature));
    }

    #[test]
    fn test_aggregate_and_aggregate_verify() {
        let ikm1 = b"key material for signer 1..........................";
        let ikm2 = b"key material for signer 2..........................";
        let salt = b"BLS-SIG-KEYGEN-SALT-";

        let sk1 = keygen(ikm1, salt, None).unwrap();
        let sk2 = keygen(ikm2, salt, None).unwrap();

        let pk1 = sk_to_pk(&sk1);
        let pk2 = sk_to_pk(&sk2);

        let message1 = b"Message for signer 1";
        let message2 = b"Message for signer 2";

        let sig1 = sign(&sk1, message1);
        let sig2 = sign(&sk2, message2);

        let aggregated = aggregate(&[&sig1, &sig2]).unwrap();

        let valid = aggregate_verify(&[&pk1, &pk2], &[message1, message2], &aggregated);
        assert!(valid);

        // With an invalid public key the aggregated verification should fail.
        let invalid = aggregate_verify(&[&pk1, b"invalid pk"], &[message1, message2], &aggregated);
        assert!(!invalid);
    }
}
