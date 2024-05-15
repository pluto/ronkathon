//! Does the SRS setup for the KZG10 scheme.

use super::*;

/// simple setup to get params.
#[allow(dead_code, clippy::type_complexity)]
fn setup() -> (Vec<AffinePoint<PlutoBaseCurve>>, Vec<AffinePoint<PlutoExtendedCurve>>) {
  // NOTE: For demonstration purposes only.

  // This is just tau from plonk by hand, it is not actually secure
  let tau: u32 = 2;

  // NOTE: Just sample the d of both for now.
  // - g1 and g2 SRS have variable sizes for diff kzg uses
  // - in eth blobs, g1 is 4096 elements, g2 is 16 elements
  // - in plonk, we need d+5 g1 elements and one g2 element
  let mut srs_g1_points: Vec<AffinePoint<PlutoBaseCurve>> = vec![];
  let mut srs_g2_points: Vec<AffinePoint<PlutoExtendedCurve>> = vec![];
  for i in 0..7 {
    // G1 Group

    // degree seven commitment poly
    let result = AffinePoint::<PlutoBaseCurve>::generator() * tau.pow(i);
    srs_g1_points.push(result);
    // G2 Group

    // degree two divisor poly
    if i < 2 {
      let result = AffinePoint::<PlutoExtendedCurve>::generator() * tau.pow(i);
      srs_g2_points.push(result);
    }
  }

  (srs_g1_points, srs_g2_points)
}

/// kzg poly commit
#[allow(dead_code)]
fn commit(
  coefs: Vec<u32>,
  g1_srs: Vec<AffinePoint<PlutoBaseCurve>>,
) -> AffinePoint<PlutoBaseCurve> {
  // commit to a polynomial
  // - given a polynomial, commit to it
  assert!(g1_srs.len() >= coefs.len());
  // Todo implement multiplication with field elements as scalar mult.
  // Maybe having the scalar mult be around the base field like colin suggested is better

  let mut commitment = AffinePoint::Infinity;
  for (coef, point) in coefs.iter().zip(g1_srs) {
    let res = point * *coef;
    // println!("res {:?}, of multiplying point {:?}, and coef {:?}", res, point, coef);
    println!("commitment {:?} before addition with {:?}", commitment, res);
    commitment = commitment + res;
  }
  commitment
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
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(1), PlutoBaseField::new(2)),
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(68), PlutoBaseField::new(74)),
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(65), PlutoBaseField::new(98)),
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(18), PlutoBaseField::new(49)),
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(1), PlutoBaseField::new(99)),
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(68), PlutoBaseField::new(27)),
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(65), PlutoBaseField::new(3)),
    ];

    assert_eq!(g1srs, expected_g1srs);

    println!("g2srs {:?}", g2srs);
    let expected_2g = AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::new([PlutoBaseField::new(90), PlutoBaseField::ZERO]),
      PlutoBaseFieldExtension::new([PlutoBaseField::ZERO, PlutoBaseField::new(82)]),
    );

    let g2_gen = AffinePoint::<PlutoExtendedCurve>::generator();
    let expected_g2srs = vec![g2_gen, expected_2g];

    assert_eq!(g2srs, expected_g2srs);
  }

  #[test]
  fn test_commit() {
    let (g1srs, _) = setup();
    // p(x) = (x-1)(x-2)(x-3)
    // p(x) = x^3 - 6x^2 + 11x - 6
    // -> -6 mod 17 is 11 so this is [1, 11, 11, 1]
    let coefficients = vec![11, 11, 11, 1];
    //  g1srs[0] * 11 + g1srs[1] * 11 + g1srs[2] * 11 + g1srs[3] * 1
    let commit_1 = commit(coefficients, g1srs.clone());
    assert_eq!(commit_1, AffinePoint::<PlutoBaseCurve>::Infinity);

    // p(x) = (x-1)(x-2)(x-3)(x-4)
    // p(x) = x^4 - 10x^3 + 35x^2 - 50x + 24
    // -> 24 mod 17 is 7
    // -> 50 mod 17 is 16
    // -> 35 mod 17 is 1
    // coefficients = [7, 16, 1, 11, 1]
    let coefficients = vec![7, 16, 1, 11, 1];
    //  g1srs[0] * 7 + g1srs[1] * 16 + g1srs[2] * 1 + g1srs[3] * 11 + g1srs[4] * 1
    let commit_2 = commit(coefficients, g1srs.clone());
    assert_eq!(
      commit_2,
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(32), PlutoBaseField::new(59))
    );

    // p(x)  = x^2 + 2x + 3
    let coefficients = vec![3, 2, 1];
    // g1srs[0] * 3 + g1srs[1] * 2  + g1srs[2] * 1
    let commit_3 = commit(coefficients, g1srs);
    assert_eq!(
      commit_3,
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(32), PlutoBaseField::new(59))
    );
  }
}
