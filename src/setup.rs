//! Does the SRS setup for the KZG10 scheme.

use super::*;

#[allow(dead_code, clippy::type_complexity)]
fn setup() -> (Vec<AffinePoint<PlutoCurve<GF101>>>, Vec<AffinePoint<PlutoCurve<Ext<2, GF101>>>>) {
  // NOTE: For demonstration purposes only.

  // This is just tau from plonk by hand, it is not actually secure
  let tau = 2;

  // NOTE: Just sample the d of both for now.
  // - g1 and g2 SRS have variable sizes for diff kzg uses
  // - in eth blobs, g1 is 4096 elements, g2 is 16 elements
  // - in plonk, we need d+5 g1 elements and one g2 element
  let mut srs_g1_points: Vec<AffinePoint<PlutoCurve<GF101>>> = vec![];
  let mut srs_g2_points: Vec<AffinePoint<PlutoCurve<Ext<2, GF101>>>> = vec![];
  for i in 0..7 {
    // G1 Group
    let t_power = GF101::new(field::powmod(tau, i, 101));
    // degree seven commitment poly
    let result = AffinePoint::<PlutoCurve<GF101>>::generator() * t_power;
    srs_g1_points.push(result);
    // G2 Group

    // degree two divisor poly
    if i < 2 {
      let result = AffinePoint::<PlutoCurve<Ext<2, GF101>>>::generator() * t_power;
      srs_g2_points.push(result);
    }
  }

  (srs_g1_points, srs_g2_points)
}

fn commit(
  coefs: Vec<GF101>,
  g1_srs: Vec<AffinePoint<PlutoCurve<GF101>>>,
) -> AffinePoint<PlutoCurve<GF101>> {
  // commit to a polynomial
  // - given a polynomial, commit to it
  assert!(g1_srs.len() >= coefs.len());
  // Todo implement multiplication with field elements as scalar mult.
  // Maybe having the scalar mult be around the base field like colin suggested is better
  return g1_srs
    .iter()
    .zip(coefs.iter())
    .map(|(point, &coef)| *point * coef)
    .reduce(|x, y| x + y)
    .expect("srs not large enough");
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
      AffinePoint::<PlutoCurve<GF101>>::new(GF101::new(1), GF101::new(2)),
      AffinePoint::<PlutoCurve<GF101>>::new(GF101::new(68), GF101::new(74)),
      AffinePoint::<PlutoCurve<GF101>>::new(GF101::new(65), GF101::new(98)),
      AffinePoint::<PlutoCurve<GF101>>::new(GF101::new(18), GF101::new(49)),
      AffinePoint::<PlutoCurve<GF101>>::new(GF101::new(1), GF101::new(99)),
      AffinePoint::<PlutoCurve<GF101>>::new(GF101::new(68), GF101::new(27)),
      AffinePoint::<PlutoCurve<GF101>>::new(GF101::new(65), GF101::new(3)),
    ];
    assert_eq!(g1srs, expected_g1srs);

    println!("g2srs {:?}", g2srs);
    let expected_2g = AffinePoint::<PlutoCurve<Ext<2, GF101>>>::new(
      Ext::<2, GF101>::new([GF101::new(90), GF101::ZERO]),
      Ext::<2, GF101>::new([GF101::ZERO, GF101::new(82)]),
    );

    let g2_gen = AffinePoint::<PlutoCurve<Ext<2, GF101>>>::generator();
    let expected_g2srs = vec![g2_gen, expected_2g];

    assert_eq!(g2srs, expected_g2srs);
  }

  #[test]
  fn test_commit() {
    let (g1srs, _) = setup();
    println!("g1srs {:?}", g1srs);

    // A univariate polynomial with roots 1,2,3 converted into coefficient form for simplicity.
    //
    // p(x) = (x-1)(x-2)(x-3)
    // p(x) = x^3 - 6x^2 + 11x - 6
    //
    let coefficients = vec![-GF101::new(6), GF101::new(11), -GF101::new(6), GF101::new(1)];
    let polynomial = Polynomial::<Monomial, GF101>::new(coefficients);
    println!("polynomial {:?}", polynomial);
    let commit = commit(polynomial.coefficients, g1srs);
    println!("commit {:?}", commit);
    assert_eq!(commit, AffinePoint::<PlutoCurve<GF101>>::new(GF101::new(1), GF101::new(2)));
  }
}
