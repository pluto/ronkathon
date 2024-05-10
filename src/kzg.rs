use ark_bn254::{Bn254, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::Field;
use ark_poly::DenseUVPolynomial;
use num_bigint::BigUint;
use rand::thread_rng;

use super::*;

// simple setup to get params.
pub fn setup(d: u64) -> (Vec<G1Affine>, Vec<G2Affine>) {
  // NOTE: For demonstration purposes only.
  // Create some toxic waste, typically done in MPC and discarded.
  let mut rng = thread_rng();
  let mut tau_bytes = vec![0u8; 32];
  rng.fill(&mut tau_bytes[..]);
  println!("tau_toxic_waste={:?}", BigUint::from_bytes_le(&tau_bytes));

  let tau = Fr::from(BigUint::from_bytes_le(&tau_bytes));
  // let tau = Fr::rand(&mut rng);

  // NOTE: Just sample the d of both for now.
  // - g1 and g2 SRS have variable sizes for diff kzg uses
  // - in eth blobs, g1 is 4096 elements, g2 is 16 elements
  // - in plonk, we need d+5 g1 elements and one g2 element
  let mut srs_g1_points: Vec<G1Affine> = vec![];
  let mut srs_g2_points: Vec<G2Affine> = vec![];
  for i in 1..d + 1 {
    // G1 Group
    let result = G1Projective::from(G1Affine::generator()) * tau.pow([i]);
    srs_g1_points.push(result.into_affine());

    // G2 Group
    let result = G2Projective::from(G2Affine::generator()) * tau.pow([i]);
    srs_g2_points.push(result.into_affine());
  }

  (srs_g1_points, srs_g2_points)
}

// kzg commit
pub fn commit<const MSM: bool>(coefs: Vec<Fr>, g1_srs: Vec<G1Affine>) -> G1Affine {
  assert!(g1_srs.len() >= coefs.len());

  // fiddle with arkworks too
  if MSM {
    return <G1Projective as VariableBaseMSM>::msm(&g1_srs[..coefs.len()], &coefs)
      .expect("failed msm")
      .into_affine();
  }

  return g1_srs
    .iter()
    .zip(coefs)
    .map(|x| G1Projective::from(*x.0) * x.1)
    .reduce(|x, y| x + y)
    .expect("srs not large enough")
    .into_affine();
}

// divide the poly by the point to find the witness poly
pub fn open(coefs: Vec<Fr>, point: Fr, g1_srs: Vec<G1Affine>) -> G1Affine {
  use std::ops::Div;

  use ark_poly::univariate::DensePolynomial;

  // arkworks for now
  let poly = DensePolynomial::from_coefficients_vec(coefs);
  let divisor = DensePolynomial::from_coefficients_vec(vec![-point, Fr::ONE]);

  commit::<false>(poly.div(&divisor).coeffs, g1_srs)
}

pub fn check(
  p: G1Affine,
  q: G1Affine,
  point: Fr,
  value: Fr,
  g1_srs: Vec<G1Affine>,
  g2_srs: Vec<G2Affine>,
) -> bool {
  use ark_ec::pairing::Pairing;

  let g1 = *g1_srs.first().expect("has g1 srs");
  let g2 = *g2_srs.first().expect("has g2 srs");

  let lhs = Bn254::pairing(q, g2.into_group() - G2Affine::generator() * point);
  let rhs = Bn254::pairing(p.into_group() - g1 * value, G2Affine::generator());

  lhs == rhs
}

pub fn evaluate(coefs: Vec<Fr>, point: Fr) -> Fr {
  coefs
    .iter()
    .enumerate()
    .map(|x| {
      let exp = x.0 as u64;
      x.1 * &point.pow([exp])
    })
    .reduce(|x, y| x + y)
    .unwrap()
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_e2e() {
    // A univariate polynomial with roots 1,2,3 converted into coefficient form for simplicity.
    //
    // p(x) = (x-1)(x-2)(x-3)
    // p(x) = x^3 - 6x^2 + 11x - 6
    //
    // Now, for example, prove that p(4) = 6 via witness commit q(x) = x^2 - 2x + 3
    //

    // Poor man's polynomial
    let p = vec![Fr::from(-6), Fr::from(11), Fr::from(-6), Fr::from(1)];
    let x = Fr::from(4);
    let y = evaluate(p.clone(), x);

    let (g1_srs, g2_srs) = setup(10);
    let p_commit = commit::<false>(p.clone(), g1_srs.clone());
    let q_commit = open(p.clone(), x, g1_srs.clone());
    let valid = check(p_commit, q_commit, x, y, g1_srs.clone(), g2_srs.clone());

    println!("p_commit={}", p_commit);
    println!("q_commit={}", q_commit);

    assert!(valid);
  }
}
