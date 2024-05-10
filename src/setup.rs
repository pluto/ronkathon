#![allow(unused_imports)]
use super::*;
use crate::curves::{g1_curve::C101, g2_curve::G2Curve, AffinePoint};

// hardcoded degree for now
#[allow(dead_code)]
fn setup() -> (Vec<AffinePoint<C101>>, Vec<AffinePoint<G2Curve>>) {
  // NOTE: For demonstration purposes only.

  // This is just tau from plonk by hand, it is not actually secure
  let tau: u32 = 2;

  // NOTE: Just sample the d of both for now.
  // - g1 and g2 SRS have variable sizes for diff kzg uses
  // - in eth blobs, g1 is 4096 elements, g2 is 16 elements
  // - in plonk, we need d+5 g1 elements and one g2 element
  let mut srs_g1_points: Vec<AffinePoint<C101>> = vec![];
  let mut srs_g2_points: Vec<AffinePoint<G2Curve>> = vec![];
  for i in 0..7 {
    // G1 Group

    // degree seven commitment poly
    let result = AffinePoint::<C101>::generator() * tau.pow(i);
    srs_g1_points.push(result);
    // G2 Group

    // degree two divisor poly
    if i < 2 {
      let result = AffinePoint::<G2Curve>::generator() * tau.pow(i);
      srs_g2_points.push(result);
    }
  }

  (srs_g1_points, srs_g2_points)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::field::gf_101_2::Ext2;

  #[test]
  fn test_setup() {
    let (g1srs, g2srs) = setup();
    assert!(g1srs.len() == 7);
    assert!(g2srs.len() == 2);
    let expected_g1srs = vec![
      AffinePoint::<C101>::new(GF101::new(1), GF101::new(2)),
      AffinePoint::<C101>::new(GF101::new(68), GF101::new(74)),
      AffinePoint::<C101>::new(GF101::new(65), GF101::new(98)),
      AffinePoint::<C101>::new(GF101::new(18), GF101::new(49)),
      AffinePoint::<C101>::new(GF101::new(1), GF101::new(99)),
      AffinePoint::<C101>::new(GF101::new(68), GF101::new(27)),
      AffinePoint::<C101>::new(GF101::new(65), GF101::new(3)),
    ];
    assert_eq!(g1srs, expected_g1srs);

    println!("g2srs {:?}", g2srs);
    let expected_2g = AffinePoint::<G2Curve>::new(
      Ext2::<GF101>::new(GF101::new(90), GF101::ZERO),
      Ext2::<GF101>::new(GF101::ZERO, GF101::new(82)),
    );

    let g2_gen = AffinePoint::<G2Curve>::generator();
    let expected_g2srs = vec![g2_gen, expected_2g];

    assert_eq!(g2srs, expected_g2srs);
  }
}
