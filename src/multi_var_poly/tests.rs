use super::*;

#[test]
fn test_multivar_polynomial_evaluation() {
  // Create a polynomial: f(x, y) = 2x^2 y + 3xy + 1
  let degree = [2, 1]; // Degree 2 in x, degree 1 in y
  let coefficients = vec![
    PlutoBaseField::new(1), // Constant term
    PlutoBaseField::new(0), // Coefficient of y
    PlutoBaseField::new(0), // Coefficient of x
    PlutoBaseField::new(3), // Coefficient of xy
    PlutoBaseField::new(0), // Coefficient of x^2
    PlutoBaseField::new(2), // Coefficient of yx^2
  ];

  let poly = MultiVarPolynomial::<PlutoBaseField, 2>::new(degree, coefficients).unwrap();

  // Evaluate the polynomial at (x, y) = (2, 3)
  let result = poly.evaluation([PlutoBaseField::new(2), PlutoBaseField::new(3)]);

  // Calculate the expected result
  let expected = PlutoBaseField::new(43);

  println!("f(2, 3) = {:?}", result);
  assert_eq!(result, expected);
}
