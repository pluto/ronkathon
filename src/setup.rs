//! Does the SRS setup for the KZG10 scheme.

use super::*;

#[allow(dead_code, clippy::type_complexity)]
fn setup() -> (
  Vec<AffinePoint<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>>,
  Vec<AffinePoint<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>>>,
) {
  // NOTE: For demonstration purposes only.

  // This is just tau from plonk by hand, it is not actually secure
  let tau: u32 = 2;

  // NOTE: Just sample the d of both for now.
  // - g1 and g2 SRS have variable sizes for diff kzg uses
  // - in eth blobs, g1 is 4096 elements, g2 is 16 elements
  // - in plonk, we need d+5 g1 elements and one g2 element
  let mut srs_g1_points: Vec<AffinePoint<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>> =
    vec![];
  let mut srs_g2_points: Vec<
    AffinePoint<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>>,
  > = vec![];
  for i in 0..7 {
    // G1 Group

    // degree seven commitment poly
    let result = AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::generator()
      * tau.pow(i);
    srs_g1_points.push(result);
    // G2 Group

    // degree two divisor poly
    if i < 2 {
      let result =
        AffinePoint::<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>>::generator()
          * tau.pow(i);
      srs_g2_points.push(result);
    }
  }

  (srs_g1_points, srs_g2_points)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_setup() {
    let (g1srs, g2srs) = setup();
    assert!(g1srs.len() == 7);
    assert!(g2srs.len() == 2);
    let expected_g1srs = vec![
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(2),
      ),
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(68),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(74),
      ),
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(65),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(98),
      ),
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(18),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(49),
      ),
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(99),
      ),
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(68),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(27),
      ),
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(65),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
      ),
    ];
    assert_eq!(g1srs, expected_g1srs);

    println!("g2srs {:?}", g2srs);
    let expected_2g = AffinePoint::<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>>::new(
      GaloisField::<2, { PlutoPrime::Base as usize }>::new([
        PrimeField::<{ PlutoPrime::Base as usize }>::new(90),
        PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
      ]),
      GaloisField::<2, { PlutoPrime::Base as usize }>::new([
        PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
        PrimeField::<{ PlutoPrime::Base as usize }>::new(82),
      ]),
    );

    let g2_gen =
      AffinePoint::<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>>::generator();
    let expected_g2srs = vec![g2_gen, expected_2g];

    assert_eq!(g2srs, expected_g2srs);
  }
}
