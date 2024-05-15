//! Pairing operations for the Pluto curve.

use super::*;

// TODO: I believe we will definitely need to construct GF(17) outright, as we will need to perform
// arithmetic operations on it.

// TODO: I think we also need to create something like a `struct Torsion<const R: usize>` to have a
// representation of the r-torsion points on the curve. These may have to just be for our curve and
// not generic as making them generic could be quite hard.

/// Compute the Tate pairing of two points on the curve.
pub fn pairing<const R: usize>(
  p: AffinePoint<PlutoExtendedCurve>,
  q: AffinePoint<PlutoExtendedCurve>,
) -> GaloisField<2, { PlutoPrime::Base as usize }> {
  // Check that both inputs are r torsion points on the curve
  let mut result = p;
  for _ in 0..R {
    result += p;
  }
  assert_eq!(result, p);
  let mut result = q;
  for _ in 0..R {
    result += q;
  }
  assert_eq!(result, q);

  // Compute the Miller loop
  todo!();
}

fn miller_loop<const R: usize>(
  _p: AffinePoint<PlutoExtendedCurve>,
  _q: AffinePoint<PlutoExtendedCurve>,
) -> GaloisField<2, { PlutoPrime::Base as usize }> {
  // Use the R to get a binary representation, then loop over the binary representation to do the
  // algorithm.
  todo!();
}

fn line_function<const R: usize>(
  a: AffinePoint<PlutoExtendedCurve>,
  b: AffinePoint<PlutoExtendedCurve>,
  input: AffinePoint<PlutoExtendedCurve>,
) -> GaloisField<2, { PlutoPrime::Base as usize }> {
  let (a_x, a_y) = match a {
    AffinePoint::PointOnCurve(x, y) => (x, y),
    AffinePoint::Infinity => panic!("Cannot use point at infinity"),
  };
  let (b_x, b_y) = match b {
    AffinePoint::PointOnCurve(x, y) => (x, y),
    AffinePoint::Infinity => panic!("Cannot use point at infinity"),
  };
  let (input_x, input_y) = match input {
    AffinePoint::PointOnCurve(x, y) => (x, y),
    AffinePoint::Infinity => panic!("Cannot use point at infinity"),
  };
  // TODO: Add explanation for these equations.
  // The case for a general (secant) line
  if a_x == b_x {
    let m = (b_y - a_y) / (b_x - a_x);
    m * (input_x - a_x) + a_y - input_y
  }
  // The case with a tangent line (I believe since if a_y == b_y then a_x == b_x, so this is true
  // just by checking the first condition)
  else if a_y == b_y {
    let m = <GaloisField<2, { PlutoPrime::Base as usize }>>::from(3_usize) * a_x.pow(2)
      / (<GaloisField<2, { PlutoPrime::Base as usize }>>::from(2_usize) * a_y);
    m * (input_x - a_x) + a_y - input_y
  }
  // The case for a vertical line
  else {
    input_x - a_x
  }
}
