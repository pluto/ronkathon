// File: examples/sum_check_demo.rs

use ronkathon::{
  algebra::field::prime::PlutoBaseField, multi_var_poly::MultiVarPolynomial, sumcheck::SumCheck,
};

type F = PlutoBaseField;

fn create_demo_polynomial() -> MultiVarPolynomial<F> {
  // Create the polynomial:
  // 3 x^2 y^2 z^2 + 2x^2 y + 5x^2 z^2 + 4yz + 6x + 1
  let coordinates = vec![
    vec![0, 0, 0], // Constant term
    vec![1, 0, 0], // x term
    vec![0, 1, 1], // yz term
    vec![2, 0, 2], // x^2 z^2 term
    vec![2, 1, 0], // x^2 y term
    vec![2, 2, 2], // x^2 y^2 z^2 term
  ];
  let coefficients = vec![
    F::from(1), // Constant term
    F::from(6), // x term
    F::from(4), // yz term
    F::from(5), // x^2 z^2 term
    F::from(2), // x^2 y term
    F::from(3), // x^2 y^2 z^2 term
  ];
  MultiVarPolynomial::from_coordinates(coordinates, coefficients).unwrap()
}

fn main() {
  println!("Sum-Check Protocol Demonstration");
  println!("================================");

  let poly = create_demo_polynomial();
  println!("Created multivariate polynomial:");
  println!("3 x^2 y^2 z^2 + 2x^2 y + 5x^2 z^2 + 4yz + 6x + 1");

  let expected_sum = F::from(57);
  println!("\nExpected sum over boolean hypercube: {:?}", expected_sum);

  let mut sumcheck = SumCheck::new(poly, true);
  println!("\nRunning interactive sum-check protocol:");
  sumcheck.run_interactive_protocol();

  println!("\nVerification result:");
  if sumcheck.verifier.result == expected_sum {
    println!("Sum-check protocol succeeded! The sum is verified to be {:?}", expected_sum);
  } else {
    println!(
      "Sum-check protocol failed. Expected {:?}, but got {:?}",
      expected_sum, sumcheck.verifier.result
    );
  }
}
