use num_bigint::BigUint;
use rand::{thread_rng, Rng};

use crate::{
  curves::{g1_curve::C101, g2_curve::G2Curve, AffinePoint, CurveParams},
  field::{gf_101::GF101, FiniteField},
};

fn setup(degree: u32) -> (Vec<AffinePoint<C101>>, Vec<AffinePoint<G2Curve>>) {
  // NOTE: For demonstration purposes only.
  // Create some toxic waste, typically done in MPC and discarded.
  let mut rng = thread_rng();
  let mut tau_bytes = [0u8; 4];
  rng.fill(&mut tau_bytes[..]);
  //   println!("tau_toxic_waste={:?}", BigUint::from_bytes_le(&tau_bytes));

  // This does get concatenated rn
  let tau = GF101::from_canonical_u32(u32::from_le_bytes(tau_bytes));

  // let tau = Fr::rand(&mut rng);

  // NOTE: Just sample the d of both for now.
  // - g1 and g2 SRS have variable sizes for diff kzg uses
  // - in eth blobs, g1 is 4096 elements, g2 is 16 elements
  // - in plonk, we need d+5 g1 elements and one g2 element
  let mut srs_g1_points: Vec<AffinePoint<C101>> = vec![];
  let mut srs_g2_points: Vec<AffinePoint<G2Curve>> = vec![];
  //   for i in 1..degree + 1 {
  //     // G1 Group
  //     let result = AffinePoint::<C101>::generator() *
  // tau.pow(field::gf_101::GF101::Storage::from(i));     srs_g1_points.push(result);

  //     // G2 Group
  //     let result = AffinePoint::<G2Curve>::generator() * tau.pow(i as u32);
  //     srs_g2_points.push(result);
  //   }

  (srs_g1_points, srs_g2_points)
}

mod tests {
  use super::*;

  #[test]
  fn test_setup() {
    let (g1, g2) = setup(5);
    println!("{:?}", g1);
    println!("{:?}", g2);
  }
}
