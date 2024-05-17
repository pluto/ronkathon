//! Pairing operations for the Pluto curve.

use super::*;

/// Compute the Tate pairing of two points on the curve.
/// The pairing is a bilinear map from G x G -> F_{p^k} where G is the group of R-torsion points on
/// the curve and F_{p^k} is an extension with embedding degree k. In particular, the second copy of
/// G is acted on by a map to assure that it is a distinct set of R-torsion points.
///
/// ## Arguments
/// * `const R` - The order of the R-torsion group.
/// * `p` - The first point in the pairing which must be a point in the R-torsion group.
/// * `q` - The second point in the pairing which must be a point in the R-torsion group that
///   generates a distinct "petal" of the R-torsion group.
///
/// ## Returns
/// The result of the pairing.
///
/// ## Panics
/// Panics if either input is not in the R-torsion group via an exhaustive check that the point
/// added to itself R times is the point itself for both inputs.
///
/// ## Notes
/// This uses the [Miller loop](https://crypto.stanford.edu/pbc/notes/ep/miller.html) algorithm to compute the pairing.
pub fn pairing<C: EllipticCurve + fmt::Debug + PartialEq, const R: usize>(
  p: AffinePoint<C>,
  q: AffinePoint<C>,
) -> C::BaseField {
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
  let val = miller_loop::<C, R>(p, q);

  // Do the final exponentiation
  val.pow((C::BaseField::ORDER - 1) / R)
}

pub(crate) fn miller_loop<C: EllipticCurve + fmt::Debug + PartialEq, const R: usize>(
  p: AffinePoint<C>,
  q: AffinePoint<C>,
) -> C::BaseField {
  // Use the R to get a binary representation, then loop over the binary representation to do the
  // algorithm.
  let mut x = C::BaseField::ONE;
  let mut z = p;

  let r = format!("{:b}", R);
  for bit in r.chars().skip(1) {
    x = x.pow(2) * tangent_line::<C>(z, q) / vertical_line(2 * z, q);
    z += z;
    if bit == '1' {
      if z + p == AffinePoint::Infinity {
        x *= line_function::<C>(z, p, q);
      } else {
        x = x * line_function::<C>(z, p, q) / vertical_line(z + p, q);
      }
      z += p;
    }
  }
  x
}

/// Creates a line function through the given points `a` and `b` and evaluates it at the point
/// `input`.
///
/// ## Arguments
/// * `a` - The first point on the line.
/// * `b` - The second point on the line.
/// * `input` - The point at which to evaluate the line.
///
/// ## Returns
/// The value of the line function at the point `input`.
///
/// ## Panics
/// Panics if either `a`, `b`, or `input` are the point at infinity.
pub fn line_function<C: EllipticCurve>(
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

  // The case for a general (secant) line
  if a_x != b_x {
    let m = (b_y - a_y) / (b_x - a_x);
    m * (input_x - a_x) + a_y - input_y
  }
  // The case with a tangent line since if a_y == b_y then a_x == b_x, so this is true
  // just by checking the first condition.
  else if a_y == b_y {
    let m = (<C::BaseField>::from(3_usize) * a_x.pow(2) + C::EQUATION_A.into())
      / (<C::BaseField>::from(2_usize) * a_y);
    m * (input_x - a_x) + a_y - input_y
  }
  // The case for a vertical line as we must only have the case where `a_x == b_x` remaining.
  else {
    input_x - a_x
  }
}

/// Creates a vertical line through the given point `a` and evaluates it at the point `input`.
/// This is a special case of the line function where the two points used to construct the line can
/// be found just from one input.
///
/// ## Arguments
/// * `a` - The point at which we create a vertical line going through.
/// * `input` - The point at which to evaluate the line.
///
/// ## Returns
/// The value of the line function at the point `input`.
///
/// ## Panics
/// Panics if either `a` or `input` are the point at infinity
pub fn vertical_line<C: EllipticCurve>(a: AffinePoint<C>, input: AffinePoint<C>) -> C::BaseField {
  line_function::<C>(a, -a, input)
}

/// Creates a tangent line through the given point `a` and evaluates it at the point `input`.
/// This is a special case of the line function where the two points used to construct the line can
/// be found just from one input.
///
/// ## Arguments
/// * `a` - The point at which we create a tangent line going through.
/// * `input` - The point at which to evaluate the line.
///
/// ## Returns
/// The value of the line function at the point `input`.
///
/// ## Panics
/// Panics if either `a` or `input` are the point at infinity.
pub fn tangent_line<C: EllipticCurve>(a: AffinePoint<C>, input: AffinePoint<C>) -> C::BaseField {
  line_function::<C>(a, a, input)
}

impl Distribution<AffinePoint<PlutoBaseCurve>> for Standard {
  #[inline]
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> AffinePoint<PlutoBaseCurve> {
    loop {
      let x = PlutoBaseField::new(rng.next_u64() as usize);
      let rhs = x.pow(3) + PlutoBaseCurve::EQUATION_A * x + PlutoBaseCurve::EQUATION_B;
      if rhs.euler_criterion() {
        // Flip a coin and pick the square root
        if rand::random::<bool>() {
          return AffinePoint::new(x, rhs.sqrt().unwrap().0);
        } else {
          return AffinePoint::new(x, rhs.sqrt().unwrap().1);
        }
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn random_point() {
    let mut rng = rand::thread_rng();
    let point = rng.gen::<AffinePoint<PlutoBaseCurve>>();
    println!("Random point: {:?}", point);
  }

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

  #[test]
  fn pairing_test() {
    let p = AffinePoint::<PlutoExtendedCurve>::from(AffinePoint::<PlutoBaseCurve>::generator());
    let cube_root_of_unity = PlutoBaseFieldExtension::primitive_root_of_unity(3);
    let q = if let AffinePoint::<PlutoBaseCurve>::Point(x, y) =
      AffinePoint::<PlutoBaseCurve>::generator()
    {
      AffinePoint::<PlutoExtendedCurve>::new(
        cube_root_of_unity * PlutoBaseFieldExtension::from(x),
        PlutoBaseFieldExtension::from(y),
      )
    } else {
      panic!("Generator is not a point");
    };

    let result = pairing::<PlutoExtendedCurve, 17>(p, q);
    println!("Pairing result: {:?}", result);

    assert_eq!(result.pow(17), PlutoBaseFieldExtension::ONE);
  }
}
