//! Pairing operations for the Pluto curve.

use std::fmt::Debug;

use super::*;

/// Compute the simplified Tate pairing of two points on the curve.
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
/// The result of the pairing, an element of rth root of unity in base field of the curve.
///
/// ## Panics
/// Panics if either input is not in the R-torsion group via an exhaustive check that the point
/// added to itself R times is the point itself for both inputs.
///
/// ## Notes
/// This uses the [Miller loop](https://crypto.stanford.edu/pbc/notes/ep/miller.html) algorithm to compute the rational map required for pairing.
/// Refer to Ben Lynn's [Thesis](https://crypto.stanford.edu/pbc/thesis.pdf#page=99.18) Section 6.2.
/// Note that this is only possible for a supersingular curve and [`curve::PlutoBaseCurve`]
/// satisfies this property.
pub fn pairing<C: EllipticCurve + Debug + PartialEq, const R: usize>(
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

/// Evaluate a rational function on a divisor f_{r,P}(D_{Q}) in logarithmic time complexity using an
/// algorithm similar to double and add.
pub(crate) fn miller_loop<C: EllipticCurve + Debug + PartialEq, const R: usize>(
  p: AffinePoint<C>,
  q: AffinePoint<C>,
) -> C::BaseField {
  // Use the R to get a binary representation, then loop over the binary representation to do the
  // algorithm.
  let mut x = C::BaseField::ONE;
  let mut z = p;

  let r = format!("{:b}", R);
  let mut zeros = 0;
  for bit in r.chars().skip(1) {
    // f_{2m,P} <- f_{m,P}^2.(l_{[m]P,[m]P}(Q)/v_{[2m]P}(Q))
    let tangent = tangent_line::<C>(z, q);
    let vertical = vertical_line(2 * z, q);
    x = x.pow(2);
    if tangent == C::BaseField::ZERO {
      zeros += 1;
    } else {
      x *= tangent;
    }
    if vertical == C::BaseField::ZERO {
      zeros -= 1;
    } else {
      x /= vertical;
    }
    // Z <- 2Z
    z += z;
    if bit == '1' {
      // f_{[2m+1],P} <- f_{2m,P}.(l_{Z,P}(Q)/v_{Z+P}(Q))
      let line = line_function::<C>(z, p, q);
      if z + p == AffinePoint::Infinity {
        if line == C::BaseField::ZERO {
          zeros += 1;
        } else {
          x *= line;
        }
      } else {
        let vertical = vertical_line(z + p, q);
        if line_function::<C>(z, p, q) == C::BaseField::ZERO {
          zeros += 1;
        } else {
          x *= line;
        }
        if vertical == C::BaseField::ZERO {
          zeros -= 1;
        } else {
          x /= vertical;
        }
      }
      // Z <- Z + P
      z += p;
    }
  }

  assert_eq!(zeros, 0);
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
        }
        return AffinePoint::new(x, rhs.sqrt().unwrap().1);
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
        }
        return AffinePoint::new(x, rhs.sqrt().unwrap().1);
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  /// Compute weil pairing $w_{r} = f_{r,P}(D_Q)/f_{r,Q}(D_P)$ for points $P, Q \in E[F_{q^k}][r]$.
  /// $D_P,D_Q$ are degree zero divisors with disjoint supports to $f_{r,Q},f_{r,P}$ respectively.
  /// D_P have divisor equal to (P)-(O), and (D_Q) = (Q)-(O)
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

    // to keep the support disjoint, a random element `S` on extended curve is used, which shouldn't
    // be equal to P, -Q, P-Q
    let mut rng = rand::thread_rng();
    let mut s = rng.gen::<AffinePoint<PlutoExtendedCurve>>();
    while s == p || s == -q || s == p - q {
      s = rng.gen::<AffinePoint<PlutoExtendedCurve>>();
    }

    // (D_Q) ~ (Q+S) - (S) (equivalent divisors)
    // Compute the Miller loop for f_{r,P}(D_Q) as f_{r,P}(Q+S)/f_{r,P}(S)
    let num =
      miller_loop::<PlutoExtendedCurve, R>(p, q + s) * miller_loop::<PlutoExtendedCurve, R>(q, -s);

    // (D_P) ~ (P-S) - (-S) (equivalent divisors)
    // compute the miller loop f_{r,Q}(D_P) as f_{r,Q}(P-S)/f_{r,Q}(-S)
    let den =
      miller_loop::<PlutoExtendedCurve, R>(q, p - s) * miller_loop::<PlutoExtendedCurve, R>(p, s);

    num / den
  }

  #[test]
  fn random_point() {
    let mut rng = rand::thread_rng();
    let point = rng.gen::<AffinePoint<PlutoBaseCurve>>();
    println!("Random point: {point:?}");

    let ext_point = rng.gen::<AffinePoint<PlutoExtendedCurve>>();
    println!("Random extended point: {ext_point:?}");
  }

  #[test]
  fn cube_root_of_unity() {
    let cube_root = PlutoBaseFieldExtension::primitive_root_of_unity(3);
    assert_eq!(cube_root.pow(3), PlutoBaseFieldExtension::ONE);
    println!("Cube root of unity: {cube_root:?}");
  }

  #[test]
  fn torsion_generators() {
    let generator = AffinePoint::<PlutoBaseCurve>::GENERATOR;
    println!("Generator: {generator:?}");
    for i in 1..=PlutoPrime::Scalar as usize {
      let point = generator * PlutoScalarField::new(i);
      println!("{i:?} * P = {point:?}");
      if i == PlutoPrime::Scalar as usize {
        assert_eq!(point, AffinePoint::Infinity);
        continue;
      }
      assert!(point != AffinePoint::Infinity);
    }

    let cube_root_of_unity = PlutoBaseFieldExtension::primitive_root_of_unity(3);
    let torsion_generator = if let AffinePoint::<PlutoBaseCurve>::Point(x, y) =
      AffinePoint::<PlutoBaseCurve>::GENERATOR
    {
      AffinePoint::<PlutoExtendedCurve>::new(
        cube_root_of_unity * PlutoBaseFieldExtension::from(x),
        PlutoBaseFieldExtension::from(y),
      )
    } else {
      panic!("Generator is not a point");
    };
    for i in 1..=PlutoPrime::Scalar as usize {
      let point = torsion_generator * PlutoScalarField::new(i);
      println!("{i:?} * P = {point:?}");
      if i == PlutoPrime::Scalar as usize {
        assert_eq!(point, AffinePoint::Infinity);
        continue;
      }
      assert!(point != AffinePoint::Infinity);
    }
  }

  #[test]
  fn pairing_test() {
    let p = AffinePoint::<PlutoExtendedCurve>::from(AffinePoint::<PlutoBaseCurve>::GENERATOR);
    let cube_root_of_unity = PlutoBaseFieldExtension::primitive_root_of_unity(3);
    let q = if let AffinePoint::<PlutoBaseCurve>::Point(x, y) =
      AffinePoint::<PlutoBaseCurve>::GENERATOR
    {
      AffinePoint::<PlutoExtendedCurve>::new(
        cube_root_of_unity * PlutoBaseFieldExtension::from(x),
        PlutoBaseFieldExtension::from(y),
      )
    } else {
      panic!("Generator is not a point");
    };

    let result = pairing::<PlutoExtendedCurve, 17>(p, q);
    println!("Pairing result: {result:?}");

    assert_eq!(result.pow(17), PlutoBaseFieldExtension::ONE);
  }

  // (37*X + 9 : 93*X + 19 : 1) (63 : 35*X : 1)
  #[rstest]
  #[case(PlutoBaseFieldExtension::new([PlutoBaseField::new(9), PlutoBaseField::new(37)]),
  PlutoBaseFieldExtension::new([PlutoBaseField::new(19), PlutoBaseField::new(93)]),
  PlutoBaseFieldExtension::new([PlutoBaseField::new(63), PlutoBaseField::new(0)]),
  PlutoBaseFieldExtension::new([PlutoBaseField::new(0), PlutoBaseField::new(35)]),
  PlutoBaseFieldExtension::new([PlutoBaseField::new(31), PlutoBaseField::new(5)]),
  PlutoBaseFieldExtension::new([PlutoBaseField::new(26), PlutoBaseField::new(97)]))]
  #[case(PlutoBaseFieldExtension::new([PlutoBaseField::new(49), PlutoBaseField::new(78)]),
  PlutoBaseFieldExtension::new([PlutoBaseField::new(14), PlutoBaseField::new(42)]),
  PlutoBaseFieldExtension::new([PlutoBaseField::new(32), PlutoBaseField::new(64)]),
  PlutoBaseFieldExtension::new([PlutoBaseField::new(87), PlutoBaseField::new(59)]),
  PlutoBaseFieldExtension::new([PlutoBaseField::new(31), PlutoBaseField::new(96)]),
  PlutoBaseFieldExtension::new([PlutoBaseField::new(26), PlutoBaseField::new(4)]))]
  fn weil_tate_pairing_test(
    #[case] a_x: PlutoBaseFieldExtension,
    #[case] a_y: PlutoBaseFieldExtension,
    #[case] b_x: PlutoBaseFieldExtension,
    #[case] b_y: PlutoBaseFieldExtension,
    #[case] weil_result: PlutoBaseFieldExtension,
    #[case] tate_result: PlutoBaseFieldExtension,
  ) {
    let a = AffinePoint::<PlutoExtendedCurve>::new(a_x, a_y);
    let b = AffinePoint::<PlutoExtendedCurve>::new(b_x, b_y);

    let result = weil_pairing::<17>(a, b);
    assert_eq!(result, weil_result);

    let result = pairing::<PlutoExtendedCurve, 17>(a, b);
    assert_eq!(result, tate_result);
  }

  #[test]
  fn weil_from_tate_paring() {
    let p = AffinePoint::<PlutoExtendedCurve>::from(AffinePoint::<PlutoBaseCurve>::GENERATOR);
    let cube_root_of_unity = PlutoBaseFieldExtension::primitive_root_of_unity(3);
    let q = if let AffinePoint::<PlutoBaseCurve>::Point(x, y) =
      AffinePoint::<PlutoBaseCurve>::GENERATOR
    {
      AffinePoint::<PlutoExtendedCurve>::new(
        cube_root_of_unity * PlutoBaseFieldExtension::from(x),
        PlutoBaseFieldExtension::from(y),
      )
    } else {
      panic!("Generator is not a point");
    };

    let result = pairing::<PlutoExtendedCurve, 17>(p, q);
    let result2 = pairing::<PlutoExtendedCurve, 17>(q, p);
    let weil_from_tate_pairing = result / result2;

    let weil_pair = weil_pairing::<17>(p, q);

    assert_eq!(
      weil_pair.pow((<PlutoExtendedCurve as EllipticCurve>::BaseField::ORDER - 1) / 17),
      weil_from_tate_pairing
    );

    assert_eq!(result.pow(17), PlutoBaseFieldExtension::ONE);
  }

  // test the bilinearity of the pairing
  #[test]
  fn bilinearity() {
    let a = PlutoScalarField::new(3);
    let b = PlutoScalarField::new(5);

    let p = AffinePoint::<PlutoExtendedCurve>::from(AffinePoint::<PlutoBaseCurve>::GENERATOR);
    let cube_root_of_unity = PlutoBaseFieldExtension::primitive_root_of_unity(3);
    let q = if let AffinePoint::<PlutoBaseCurve>::Point(x, y) =
      AffinePoint::<PlutoBaseCurve>::GENERATOR
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

    println!("LHS: {lhs:?}");
    println!("RHS: {rhs:?}");

    assert_eq!(lhs, rhs);

    let r = if let AffinePoint::<PlutoBaseCurve>::Point(x, y) =
      AffinePoint::<PlutoBaseCurve>::GENERATOR.double()
    {
      AffinePoint::<PlutoExtendedCurve>::new(
        cube_root_of_unity * PlutoBaseFieldExtension::from(x),
        PlutoBaseFieldExtension::from(y),
      )
    } else {
      panic!("Generator is not a point");
    };
    let lhs = pairing::<PlutoExtendedCurve, 17>(p, q + r);
    let rhs = pairing::<PlutoExtendedCurve, 17>(p, q) * pairing::<PlutoExtendedCurve, 17>(p, r);
    assert_eq!(lhs, rhs);
  }
}
