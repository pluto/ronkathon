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

fn miller_loop<C: EllipticCurve, const R: usize>(
  _p: AffinePoint<C>,
  _q: AffinePoint<C>,
) -> C::BaseField {
  // Use the R to get a binary representation, then loop over the binary representation to do the
  // algorithm.
  todo!();
}

pub fn line_function<C: EllipticCurve, const R: usize>(
  a: AffinePoint<C>,
  b: AffinePoint<C>,
  input: AffinePoint<C>,
) -> C::BaseField {
  let (a_x, a_y) = match a {
    AffinePoint::Point(x, y) => (x, y),
    AffinePoint::Infinity => panic!("Cannot use point at infinity"),
  };
  let (b_x, b_y) = match b {
    AffinePoint::Point(x, y) => (x, y),
    AffinePoint::Infinity => panic!("Cannot use point at infinity"),
  };
  let (input_x, input_y) = match input {
    AffinePoint::Point(x, y) => (x, y),
    AffinePoint::Infinity => panic!("Cannot use point at infinity"),
  };
  // TODO: Add explanation for these equations.
  // The case for a general (secant) line
  if a_x != b_x {
    let m = (b_y - a_y) / (b_x - a_x);
    m * (input_x - a_x) + a_y - input_y
  }
  // The case with a tangent line (I believe since if a_y == b_y then a_x == b_x, so this is true
  // just by checking the first condition)
  else if a_y == b_y {
    let m = <C::BaseField>::from(3_usize) * a_x.pow(2) / (<C::BaseField>::from(2_usize) * a_y);
    m * (input_x - a_x) + a_y - input_y
  }
  // The case for a vertical line
  else {
    input_x - a_x
  }
}

pub fn vertical_line<C: EllipticCurve, const R: usize>(
  a: AffinePoint<C>,
  input: AffinePoint<C>,
) -> C::BaseField {
  line_function::<C, R>(a, -a, input)
}

// Stuff that will let us get generators of the scalar field on the base curve (which also generate
// the torsion in the extension)
impl PlutoBaseCurve {
  fn get_random_point() -> AffinePoint<PlutoBaseCurve> {
    todo!();
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn cube_root_of_unity() {
    let cube_root = PlutoBaseFieldExtension::primitive_root_of_unity(3);
    assert_eq!(cube_root.pow(3), PlutoBaseFieldExtension::ONE);
    println!("Cube root of unity: {:?}", cube_root);
  }

  #[test]
  fn torsion_generators() {
    let generator = AffinePoint::<PlutoBaseCurve>::generator();
    println!("Generator: {:?}", generator);
    for i in 1..PlutoPrime::Scalar as usize + 1 {
      let point = generator * i as u32;
      println!("{:?} * P = {:?}", i, point);
      if i == PlutoPrime::Scalar as usize {
        assert_eq!(point, AffinePoint::Infinity);

        continue;
      } else {
        assert!(point != AffinePoint::Infinity);
      }
    }

    let cube_root_of_unity = PlutoBaseFieldExtension::primitive_root_of_unity(3);
    let torsion_generator = if let AffinePoint::<PlutoBaseCurve>::Point(x, y) =
      AffinePoint::<PlutoBaseCurve>::generator()
    {
      AffinePoint::<PlutoExtendedCurve>::new(
        cube_root_of_unity * PlutoBaseFieldExtension::from(x),
        PlutoBaseFieldExtension::from(y),
      )
    } else {
      panic!("Generator is not a point");
    };
    for i in 1..PlutoPrime::Scalar as usize + 1 {
      let point = torsion_generator * i as u32;
      println!("{:?} * P = {:?}", i, point);
      if i == PlutoPrime::Scalar as usize {
        assert_eq!(point, AffinePoint::Infinity);

        continue;
      } else {
        assert!(point != AffinePoint::Infinity);
      }
    }
  }
}
