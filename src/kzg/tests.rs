use super::*;
use crate::field::prime::PlutoScalarField;

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
  let g2_gen = AffinePoint::<PlutoExtendedCurve>::generator();
  let expected_g2srs = vec![g2_gen, expected_2g];

  assert_eq!(g2srs, expected_g2srs);
}

#[test]
fn test_commit() {
  println!("FIRST COMMIT");
  let (g1srs, _) = setup();
  // p(x) = (x-1)(x-2)(x-3)
  // p(x) = - 6 + 11x -6x^2 + x^3
  // p(x) = 11 + 11x + 11x^2 + x^3 mod 17

  // -> -6 mod 17 is 11 so this is [11, 11, 11, 1]
  let coefficients = vec![
    PlutoScalarField::new(11),
    PlutoScalarField::new(11),
    PlutoScalarField::new(11),
    PlutoScalarField::new(1),
  ];
  //  g1srs[0] * 11 + g1srs[1] * 11 + g1srs[2] * 11 + g1srs[3] * 1
  let commit_1 = commit(coefficients, g1srs.clone());
  assert_eq!(commit_1, AffinePoint::<PlutoExtendedCurve>::Infinity);

  println!("\n\nSECOND COMMIT");
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
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::from(32usize),
      PlutoBaseFieldExtension::from(59usize),
    )
  );

  println!("\n\nTHIRD COMMIT");
  // p(x)  = 3 + 2x + x^2
  let coefficients =
    vec![PlutoScalarField::new(3), PlutoScalarField::new(2), PlutoScalarField::new(1)];
  // g1srs[0] * 3 + g1srs[1] * 2  + g1srs[2] * 1
  let commit_3 = commit(coefficients, g1srs);

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
  let poly = Polynomial::<Monomial, PlutoScalarField>::new(vec![
    PlutoScalarField::new(11),
    PlutoScalarField::new(11),
    PlutoScalarField::new(11),
    PlutoScalarField::new(1),
  ]);
  let eval_point = PlutoScalarField::new(4);
  //   let eval_result = poly.evaluate(eval_point);
  let commit = commit(poly.coefficients.clone(), g1srs.clone());
  assert_eq!(commit, AffinePoint::<PlutoExtendedCurve>::Infinity);
  // p(x) = (x-1)(x-2)(x-3)
  // p(x) = - 6 + 11x -6x^2 + x^3

  // divisor poly q(x) = x - 4
  // result = p(x) / q(x) = x^2 - 2x + 3
  // multiplying (1,2) * 3 + (68, 74) * 15 + (65, 98) * 1
  let open_commit = open(poly.coefficients, eval_point, g1srs.clone());
  assert_eq!(
    open_commit,
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::new([PlutoBaseField::new(26), PlutoBaseField::new(45)]),
      PlutoBaseFieldExtension::new([PlutoBaseField::ZERO, PlutoBaseField::ZERO]),
    )
  );
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
  println!("eval_result {:?}", eval_result);

  let p_commit = commit(poly.coefficients.clone(), g1srs.clone());
  // p_commit = inf
  assert_eq!(p_commit, AffinePoint::<PlutoExtendedCurve>::Infinity);
  let q_commit = open(poly.coefficients, eval_point, g1srs.clone());
  // q_commit = (26, 50)
  println!("q_commit {:?}", q_commit);

  let valid = check(p_commit, q_commit, eval_point, eval_result, g1srs.clone(), g2srs.clone());

  assert!(valid);
}
