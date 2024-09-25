use super::*;

#[test]
fn test_multivar_polynomial_evaluation() {
  // Create a polynomial: f(x, y) = 2x^2 y + 3xy + 1
  let degree = vec![2, 1]; // Degree 2 in x, degree 1 in y
  let coefficients = vec![
    PlutoBaseField::new(1), // Constant term
    PlutoBaseField::new(0), // Coefficient of y
    PlutoBaseField::new(0), // Coefficient of x
    PlutoBaseField::new(3), // Coefficient of xy
    PlutoBaseField::new(0), // Coefficient of x^2
    PlutoBaseField::new(2), // Coefficient of yx^2
  ];

  let poly = MultiVarPolynomial::<PlutoBaseField>::new(degree, coefficients).unwrap();

  // Evaluate the polynomial at (x, y) = (2, 3)
  let result = poly.evaluation(&[PlutoBaseField::new(2), PlutoBaseField::new(3)]);

  // Calculate the expected result
  let expected = PlutoBaseField::new(43);

  println!("f(2, 3) = {:?}", result);
  assert_eq!(result, expected);
}
#[test]
fn test_multivar_from_coods() {
  // Create a polynomial: f(x, y) = 2x^2 y + 3xy + 1

  let coordinates = vec![
    vec![0, 0], // Constant term
    vec![1, 1], // xy term
    vec![2, 1], // yx^2 term
  ];
  let coefficients = vec![
    PlutoBaseField::from(1), // Constant term
    PlutoBaseField::from(3), // Coefficient of xy
    PlutoBaseField::from(2), // Coefficient of yx^2
  ];
  let poly = MultiVarPolynomial::from_coordinates(coordinates, coefficients).unwrap();

  // Evaluate the polynomial at (x, y) = (2, 3)
  let result = poly.evaluation(&[PlutoBaseField::new(2), PlutoBaseField::new(3)]);

  // Calculate the expected result
  let expected = PlutoBaseField::new(43);

  println!("f(2, 3) = {:?}", result);
  assert_eq!(result, expected);
}
