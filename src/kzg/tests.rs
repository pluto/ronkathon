use algebra::group::FiniteCyclicGroup;

use super::*;
use crate::{curve::pairing::pairing, PlutoScalarField};

#[test]
fn test_setup() {
  let (g1srs, g2srs) = setup();
  assert!(g1srs.len() == 7);
  assert!(g2srs.len() == 2);
  let expected_g1srs = vec![
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::from(1usize),
      PlutoBaseFieldExtension::from(2usize),
    ),
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::from(68usize),
      PlutoBaseFieldExtension::from(74usize),
    ),
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::from(65usize),
      PlutoBaseFieldExtension::from(98usize),
    ),
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::from(18usize),
      PlutoBaseFieldExtension::from(49usize),
    ),
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::from(1usize),
      PlutoBaseFieldExtension::from(99usize),
    ),
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::from(68usize),
      PlutoBaseFieldExtension::from(27usize),
    ),
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::from(65usize),
      PlutoBaseFieldExtension::from(3usize),
    ),
  ];

  assert_eq!(g1srs, expected_g1srs);

  let expected_2g = AffinePoint::<PlutoExtendedCurve>::new(
    PlutoBaseFieldExtension::new([PlutoBaseField::new(90), PlutoBaseField::ZERO]),
    PlutoBaseFieldExtension::new([PlutoBaseField::ZERO, PlutoBaseField::new(82)]),
  );
  let g2_gen = AffinePoint::<PlutoExtendedCurve>::GENERATOR;
  let expected_g2srs = vec![g2_gen, expected_2g];

  assert_eq!(g2srs, expected_g2srs);
}

#[fixture]
fn poly_1() -> Polynomial<Monomial, PlutoScalarField, 4> {
  // p(x) = (x-1)(x-2)(x-3)
  // p(x) = - 6 + 11x -6x^2 + x^3
  // p(x) = 11 + 11x + 11x^2 + x^3 mod 17
  // -> -6 mod 17 is 11 so this is [11, 11, 11, 1]
  let a = PlutoScalarField::from(11usize);
  let b = PlutoScalarField::from(11usize);
  let c = PlutoScalarField::from(11usize);
  let d = PlutoScalarField::from(1usize);
  Polynomial::<Monomial, PlutoScalarField, 4>::new([a, b, c, d])
}

#[fixture]
fn poly_2() -> Polynomial<Monomial, PlutoScalarField, 5> {
  // p(x) = (x-1)(x-2)(x-3)(x-4)
  // p(x) = 24 - 50x + 35x^2 - 10x^3
  // -> 24 mod 17 is 7
  // -> 50 mod 17 is 16
  // -> 35 mod 17 is 1
  // coefficients = [7, 16, 1, 11, 1]
  let a = PlutoScalarField::from(7usize);
  let b = PlutoScalarField::from(16usize);
  let c = PlutoScalarField::from(1usize);
  let d = PlutoScalarField::from(11usize);
  let e = PlutoScalarField::from(1usize);
  Polynomial::<Monomial, PlutoScalarField, 5>::new([a, b, c, d, e])
}

#[fixture]
fn poly_3() -> Polynomial<Monomial, PlutoScalarField, 3> {
  // p(x)  = 3 + 2x + x^2
  let a = PlutoScalarField::from(3usize);
  let b = PlutoScalarField::from(2usize);
  let c = PlutoScalarField::from(1usize);
  Polynomial::<Monomial, PlutoScalarField, 3>::new([a, b, c])
}

#[test]
fn test_commit() {
  println!("FIRST COMMIT");
  let (g1srs, _) = setup();
  // p(x) = (x-1)(x-2)(x-3)
  // p(x) = - 6 + 11x -6x^2 + x^3
  // p(x) = 11 + 11x + 11x^2 + x^3 mod 17

  // -> -6 mod 17 is 11 so this is [11, 11, 11, 1]
  let coefficients = poly_1().coefficients;
  //  g1srs[0] * 11 + g1srs[1] * 11 + g1srs[2] * 11 + g1srs[3] * 1
  let commit_1 = commit(coefficients.to_vec(), g1srs.clone());
  assert_eq!(commit_1, AffinePoint::<PlutoExtendedCurve>::Infinity);

  println!("\n\nSECOND COMMIT");
  // p(x) = (x-1)(x-2)(x-3)(x-4)
  // p(x) = 24 - 50x + 35x^2 - 10x^3
  // -> 24 mod 17 is 7
  // -> 50 mod 17 is 16
  // -> 35 mod 17 is 1
  // coefficients = [7, 16, 1, 11, 1]
  let coefficients = poly_2().coefficients;
  //  g1srs[0] * 7 + g1srs[1] * 16 + g1srs[2] * 1 + g1srs[3] * 11 + g1srs[4] * 1
  let commit_2 = commit(coefficients.to_vec(), g1srs.clone());

  assert_eq!(
    commit_2,
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::from(32usize),
      PlutoBaseFieldExtension::from(59usize),
    )
  );

  println!("\n\nTHIRD COMMIT");
  // p(x)  = 3 + 2x + x^2
  let coefficients = poly_3().coefficients;
  // g1srs[0] * 3 + g1srs[1] * 2  + g1srs[2] * 1
  let commit_3 = commit(coefficients.to_vec(), g1srs);

  assert_eq!(
    commit_3,
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::from(32usize),
      PlutoBaseFieldExtension::from(59usize),
    )
  );
}

#[test]
fn srs_open() {
  let (g1srs, _) = setup();
  let result = g1srs[0] * PlutoScalarField::new(3);
  let result_2 = g1srs[1] * PlutoScalarField::new(15);
  let result_3 = g1srs[2] * PlutoScalarField::new(1);
  let sum = result + result_2 + result_3;
  dbg!(sum);
  assert_eq!(
    sum,
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::from(26usize),
      PlutoBaseFieldExtension::from(45usize),
    )
  );
}

#[test]
fn opening() {
  let (g1srs, _) = setup();
  println!("g1srs[0]:{:?}, g1srs[1]:{:?}, g1srs[2]:{:?}", g1srs[0], g1srs[1], g1srs[2]);
  let poly = poly_1();
  let eval_point = PlutoScalarField::new(4);
  //   let eval_result = poly.evaluate(eval_point);
  let commit = commit(poly.coefficients.clone().to_vec(), g1srs.clone());
  assert_eq!(commit, AffinePoint::<PlutoExtendedCurve>::Infinity);
  // p(x) = (x-1)(x-2)(x-3)
  // p(x) = - 6 + 11x -6x^2 + x^3

  // divisor poly q(x) = x - 4
  // result = p(x) / q(x) = x^2 - 2x + 3
  // multiplying (1,2) * 3 + (68, 74) * 15 + (65, 98) * 1
  let open_commit = open::<4>(poly.coefficients.to_vec(), eval_point, g1srs.clone());

  assert_eq!(
    open_commit,
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::from(26usize),
      PlutoBaseFieldExtension::from(45usize),
    )
  );
}

// this test was for debugging purposes
#[test]
fn all_srs_combinations() {
  let paring_params = commit_and_open(poly_1(), PlutoScalarField::new(4));

  let mut g1_index = 0;
  let mut g2_index = 0;
  let mut pairings: Vec<(GaloisField<2, 101>, GaloisField<2, 101>)> = vec![];
  #[allow(clippy::explicit_counter_loop)]
  for g1 in paring_params.g1srs {
    println!("Loop for g1 {:?}", g1);
    for g2 in &paring_params.g2srs {
      println!("Loop for g2 {:?}", g2);
      let lhs = pairing::<PlutoExtendedCurve, 17>(
        paring_params.q,
        *g2 - AffinePoint::<PlutoExtendedCurve>::GENERATOR * paring_params.point,
      );

      let rhs = pairing::<PlutoExtendedCurve, 17>(
        paring_params.p - g1 * paring_params.value,
        AffinePoint::<PlutoExtendedCurve>::GENERATOR,
      );
      if lhs == rhs {
        println!(
          "Pairing match! for g1: {:?} and g2: {:?} with g1 index {:?} and g2 index {:?}",
          g1, g2, g1_index, g2_index
        );
        println!("LHS {:?}", lhs);
        println!("RHS {:?}", rhs);
        pairings.push((lhs, rhs));
        assert_eq!(lhs, rhs);
      }
      g2_index += 1;
    }
    g1_index += 1;
  }
  assert!(!pairings.is_empty());
}

#[rstest]
#[case(poly_1(), PlutoScalarField::new(4))]
#[case(poly_2(), PlutoScalarField::new(3))]
#[case(poly_3(), PlutoScalarField::new(5))]
fn e2e<const D: usize>(
  #[case] poly: Polynomial<Monomial, PlutoScalarField, D>,
  #[case] eval_point: PlutoScalarField,
) {
  let paring_params = commit_and_open(poly, eval_point);

  // Both `p_commit` and `q_commit` are in the same group so this is good.
  // We can look at `g1srs` and see it is in `G1` and `g2srs` is in `G2`
  dbg!(paring_params.g1srs.first().unwrap());
  for i in 0..17 {
    println!("{}: {:?}", i, i * *paring_params.g1srs.first().unwrap());
  }
  assert_eq!(
    17u32 * *paring_params.g1srs.first().unwrap(),
    AffinePoint::<PlutoExtendedCurve>::Infinity
  );
  dbg!(paring_params.g2srs.first().unwrap());
  for i in 0..17 {
    println!("{}: {:?}", i, i * *paring_params.g2srs.first().unwrap());
  }
  assert_eq!(
    17u32 * *paring_params.g2srs.first().unwrap(),
    AffinePoint::<PlutoExtendedCurve>::Infinity
  );

  let valid = check(
    paring_params.p,
    paring_params.q,
    paring_params.point,
    paring_params.value,
    paring_params.g1srs.clone(),
    paring_params.g2srs.clone(),
  );
  assert!(valid);
}

#[rstest]
#[case(poly_1(), PlutoScalarField::new(4))]
#[case(poly_2(), PlutoScalarField::new(3))]
#[case(poly_3(), PlutoScalarField::new(5))]
#[should_panic]
fn invalid_check<const D: usize>(
  #[case] poly: Polynomial<Monomial, PlutoScalarField, D>,
  #[case] eval_point: PlutoScalarField,
) {
  let paring_params = commit_and_open(poly, eval_point);
  let valid = check(
    paring_params.p,
    paring_params.q,
    paring_params.point,
    PlutoScalarField::new(10), // fake evaluation point
    paring_params.g1srs.clone(),
    paring_params.g2srs.clone(),
  );
  assert!(valid);
}

#[rstest]
#[case(poly_1(), PlutoScalarField::new(4))]
#[case(poly_2(), PlutoScalarField::new(3))]
#[case(poly_3(), PlutoScalarField::new(5))]
#[should_panic]
fn fake_proof<const D: usize>(
  #[case] poly: Polynomial<Monomial, PlutoScalarField, D>,
  #[case] eval_point: PlutoScalarField,
) {
  let paring_params = commit_and_open(poly, eval_point);
  let valid = check(
    paring_params.p,
    AffinePoint::<PlutoExtendedCurve>::Infinity, // fake proof
    paring_params.point,
    paring_params.point,
    paring_params.g1srs.clone(),
    paring_params.g2srs.clone(),
  );
  assert!(valid);
}

/// Pairing params for testing pairing
pub struct PairingParams {
  pub p:     AffinePoint<PlutoExtendedCurve>,
  pub q:     AffinePoint<PlutoExtendedCurve>,
  pub point: PlutoScalarField,
  pub value: PlutoScalarField,
  pub g1srs: Vec<AffinePoint<PlutoExtendedCurve>>,
  pub g2srs: Vec<AffinePoint<PlutoExtendedCurve>>,
}

/// given a polynomial and eval point return the pairing params
pub fn commit_and_open<const D: usize>(
  poly: Polynomial<Monomial, PlutoScalarField, D>,
  eval_point: PlutoScalarField,
) -> PairingParams {
  let (g1srs, g2srs) = setup();
  let eval_result = poly.evaluate(eval_point);
  let p_commit = commit(poly.coefficients.clone().to_vec(), g1srs.clone());
  let q_commit = open::<D>(poly.coefficients.to_vec(), eval_point, g1srs.clone());
  PairingParams { p: p_commit, q: q_commit, point: eval_point, value: eval_result, g1srs, g2srs }
}

#[test]
fn pairing_params() {
  let params = commit_and_open(poly_1(), PlutoScalarField::new(4));
  assert_eq!(params.p, AffinePoint::<PlutoExtendedCurve>::Infinity);
  assert_eq!(
    params.q,
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::from(26usize),
      PlutoBaseFieldExtension::from(45usize)
    )
  );
}
