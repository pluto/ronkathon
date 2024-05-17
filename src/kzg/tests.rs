use super::*;
use crate::field::prime::PlutoScalarField;

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

/// always right polynomial with degree 0 term first
#[test]
fn test_commit() {
  let (g1srs, _) = setup();
  // p(x) = (x-1)(x-2)(x-3)
  // p(x) = - 6 + 11x -6x^2 + x^3

  // (X^2 - 3x +2)(x-3)
  // x^3 -3x^2 - 3x^2 + 9x + 2x - 6
  // x^3 - 6x^2 + 11x - 6

  // -> -6 mod 17 is 11 so this is [11, 11, 11, 1]
  let coefficients = vec![
    PlutoScalarField::new(11),
    PlutoScalarField::new(11),
    PlutoScalarField::new(11),
    PlutoScalarField::new(1),
  ];
  //  g1srs[0] * 11 + g1srs[1] * 11 + g1srs[2] * 11 + g1srs[3] * 1
  let commit_1 = commit(coefficients, g1srs.clone());
  assert_eq!(commit_1, AffinePoint::<PlutoBaseCurve>::Infinity);

  // p(x) = (x-1)(x-2)(x-3)(x-4)
  // p(x) = 24 - 50x + 35x^2 - 10x^3
  // -> 24 mod 17 is 7
  // -> 50 mod 17 is 16
  // -> 35 mod 17 is 1
  // coefficients = [7, 16, 1, 11, 1]
  let coefficients = vec![
    PlutoScalarField::new(7),
    PlutoScalarField::new(16),
    PlutoScalarField::new(1),
    PlutoScalarField::new(11),
    PlutoScalarField::new(1),
  ];
  //  g1srs[0] * 7 + g1srs[1] * 16 + g1srs[2] * 1 + g1srs[3] * 11 + g1srs[4] * 1
  let commit_2 = commit(coefficients, g1srs.clone());
  assert_eq!(
    commit_2,
    AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(32), PlutoBaseField::new(59))
  );

  // p(x)  = 3 + 2x + x^2
  let coefficients =
    vec![PlutoScalarField::new(3), PlutoScalarField::new(2), PlutoScalarField::new(1)];
  // g1srs[0] * 3 + g1srs[1] * 2  + g1srs[2] * 1
  let commit_3 = commit(coefficients, g1srs);
  assert_eq!(
    commit_3,
    AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(32), PlutoBaseField::new(59))
  );
}

#[test]
fn opening() {
  let (g1srs, _) = setup();
  let poly = Polynomial::<Monomial, PlutoScalarField>::new(vec![
    PlutoScalarField::new(11),
    PlutoScalarField::new(11),
    PlutoScalarField::new(11),
    PlutoScalarField::new(1),
  ]);
  let eval_point = PlutoScalarField::new(4);
  //   let eval_result = poly.evaluate(eval_point);
  let commit = commit(poly.coefficients.clone(), g1srs.clone());
  assert_eq!(commit, AffinePoint::<PlutoBaseCurve>::Infinity);
  // p(x) = (x-1)(x-2)(x-3)
  // p(x) = - 6 + 11x -6x^2 + x^3

  // divisor poly q(x) = x - 4
  // result = p(x) / q(x) = x^2 - 2x + 3
  let open_commit = open(poly.coefficients, eval_point, g1srs.clone());
  println!("open_commit {:?}", open_commit);
  //   assert_eq!(open, commit);
}

#[test]
fn end_to_end() {
  let (g1srs, g2srs) = setup();
  // p(x) = (x-1)(x-2)(x-3)
  // p(x) = - 6 + 11x -6x^2 + x^3
  let coefficients = vec![
    PlutoScalarField::new(11),
    PlutoScalarField::new(11),
    PlutoScalarField::new(11),
    PlutoScalarField::new(1),
  ];
  let poly = Polynomial::<Monomial, PlutoScalarField>::new(coefficients.clone());
  let eval_point = PlutoScalarField::new(4);
  let eval_result = poly.evaluate(eval_point);

  let p_commit = commit(poly.coefficients.clone(), g1srs.clone());
  // p_commit = inf
  assert_eq!(p_commit, AffinePoint::<PlutoBaseCurve>::Infinity);
  let q_commit = open(poly.coefficients, eval_point, g1srs.clone());
  // q_commit = (26, 50)
  println!("q_commit {:?}", q_commit);

  let valid = check(p_commit, q_commit, eval_point, eval_result, g1srs.clone(), g2srs.clone());

  assert!(valid);
}
