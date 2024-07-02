//! ECDH key exchange

use self::field::prime::PlutoScalarField;
use super::*;

// PARAMETERS
// *******************************************
// CURVE	the elliptic curve field and equation used
// G	    a point on the curve that generates a subgroup of large prime order n
// n	    integer order of G, means that n × G = O, n must also be prime.
// d_A	    the local private key (randomly selected) (scaler in F_n)
// Q_A	    the local public key d_A × G = Q_A (point on the curve)
// d_B	    the foreign private key (randomly selected) (scaler in F_n)
// Q_B	    the foreign public key d_B × G = Q_B (point on the curve)
// S	    the shared secret point S = d_A × Q_B = d_B × Q_A

/// SHARED SECRET COMPUTATION
/// *******************************************
/// 1. Compute the shared secret point S = d_A × Q_B.
///
/// ## Notes:
/// Elliptic Curve Diffie Hellman (ECDH) exchanges a shared secret over an insecure channel via the
/// commutativity and associativity of elliptic curve point multiplication.
///
/// d_A × (d_B × G) = d_B × (d_A × G)
///       d_B × Q_A = d_A × Q_B
pub fn compute_shared_secret(
  d_a: PlutoScalarField,
  q_b: AffinePoint<PlutoBaseCurve>,
) -> AffinePoint<PlutoBaseCurve> {
  q_b * d_a
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_key_exchange() {
    // secret keys
    let mut rns = rand::rngs::OsRng;
    let d_a = PlutoScalarField::new(rand::Rng::gen_range(&mut rns, 1..=PlutoScalarField::ORDER));
    let d_b = PlutoScalarField::new(rand::Rng::gen_range(&mut rns, 1..=PlutoScalarField::ORDER));

    // public keys
    let q_a = AffinePoint::<PlutoBaseCurve>::generator() * d_a;
    let q_b = AffinePoint::<PlutoBaseCurve>::generator() * d_b;

    // shared secret
    let s_a = compute_shared_secret(d_a, q_b);
    let s_b = compute_shared_secret(d_b, q_a);

    println!("shared secrets = [\n\t{:?},\n\t{:?}\n]", s_a, s_b);
    assert_eq!(s_a, s_b);
  }
}
