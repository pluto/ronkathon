//! Pairing operations for the Pluto curve.

use super::*;

/// Compute the Tate pairing of two points on the curve.
///
/// The pairing is a bilinear map from \mathbb{G}_1 x \mathbb{G}_2 -> \mu_{r} where
/// \mathbb{G}_{1} and \mathbb{G}_{2} are the subgroups of R-torsion group E(\mathbb{F}_{q^k})[r] on
/// the curve and \mu_{r} are rth roots of unity. In particular, the \mathbb{G}_{2} is acted on by a
/// map to assure that it is a distinct set of R-torsion points.
///
/// ## Arguments
/// * `const R` - The order of the R-torsion group.
/// * `p` - The first point in the pairing which must be a point in the base field subgroup of
///   R-torsion group.
/// * `q` - The second point in the pairing which must be a point in the R-torsion group that
///   generates a distinct "petal" of the R-torsion group.
///
/// ## Returns
/// The result of the pairing, an element of rth root of unity.
///
/// ## Panics
/// Panics if either input is not in the R-torsion group via an exhaustive check that the point
/// added to itself R times is the point itself for both inputs.
///
/// ## Notes
/// This uses the [Miller loop](https://crypto.stanford.edu/pbc/notes/ep/miller.html) algorithm to compute the rational map required for pairing.
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

/// Compute weil pairing for points P, Q
pub fn weil_pairing<const R: usize>(
  p: AffinePoint<PlutoExtendedCurve>,
  q: AffinePoint<PlutoExtendedCurve>,
) -> <PlutoExtendedCurve as EllipticCurve>::BaseField {
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

  let mut rng = rand::thread_rng();
  let mut s = rng.gen::<AffinePoint<PlutoExtendedCurve>>();
  while s == p || s == -q || s == p - q {
    s = rng.gen::<AffinePoint<PlutoExtendedCurve>>();
  }

  // Compute the Miller loop
  let num =
    miller_loop::<PlutoExtendedCurve, R>(p, q + s) * miller_loop::<PlutoExtendedCurve, R>(q, -s);

  let den =
    miller_loop::<PlutoExtendedCurve, R>(q, p - s) * miller_loop::<PlutoExtendedCurve, R>(p, s);

  num / den
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

impl Distribution<AffinePoint<PlutoExtendedCurve>> for Standard {
  #[inline]
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> AffinePoint<PlutoExtendedCurve> {
    loop {
      let x =
        PlutoBaseFieldExtension::new([rng.gen::<PlutoBaseField>(), rng.gen::<PlutoBaseField>()]);
      let rhs: PlutoBaseFieldExtension =
        x.pow(3) + x * PlutoExtendedCurve::EQUATION_A + PlutoExtendedCurve::EQUATION_B;
      if rhs.euler_criterion() {
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

    let ext_point = rng.gen::<AffinePoint<PlutoExtendedCurve>>();
    println!("Random extended point: {:?}", ext_point);
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

    let result2 = pairing::<PlutoExtendedCurve, 17>(q, p);
    println!("pairing result2: {:?}", result2);

    let weil_from_tate_pairing = result / result2;
    println!("weil from tate pairing result: {:?}", weil_from_tate_pairing);

    // let weil_pair = weil_pairing::<PlutoExtendedCurve, 17>(p, q);
    // println!("weil pairing result: {:?}", weil_pair);

    assert_eq!(result.pow(17), PlutoBaseFieldExtension::ONE);
  }

  #[test]
  fn random_test() {
    // (37*X + 9 : 93*X + 19 : 1) (63 : 35*X : 1)
    let a_x = PlutoBaseFieldExtension::new([PlutoBaseField::new(9), PlutoBaseField::new(37)]);
    let a_y = PlutoBaseFieldExtension::new([PlutoBaseField::new(19), PlutoBaseField::new(93)]);
    let a = AffinePoint::<PlutoExtendedCurve>::new(a_x, a_y);

    let b_x = PlutoBaseFieldExtension::new([PlutoBaseField::new(63), PlutoBaseField::new(0)]);
    let b_y = PlutoBaseFieldExtension::new([PlutoBaseField::new(0), PlutoBaseField::new(35)]);
    let b = AffinePoint::<PlutoExtendedCurve>::new(b_x, b_y);

    let result = weil_pairing::<17>(a, b);
    assert_eq!(
      result,
      PlutoBaseFieldExtension::new([PlutoBaseField::new(31), PlutoBaseField::new(5)])
    );
  }

  // test the bilinearity of the pairing
  #[test]
  fn bilinearity() {
    let a = PlutoScalarField::new(3);
    let b = PlutoScalarField::new(5);

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

    let a_p = p * a;
    let b_q = q * b;

    let lhs = pairing::<PlutoExtendedCurve, 17>(a_p, b_q);
    let ab = a * b;
    let rhs = pairing::<PlutoExtendedCurve, 17>(p, q).pow(ab.value);

    println!("LHS: {:?}", lhs);
    println!("RHS: {:?}", rhs);

    assert_eq!(lhs, rhs);
  }
}
