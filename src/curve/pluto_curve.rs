//! This module contains the constants and methods for the Pluto curve over the prime field `GF101`
//! and its extensions.
//!
//! The basic idea here is that we have a curve that fixes `EQUATION_A` to 0 and `EQUATION_B` to 3.
//! The rest of the properties of the curve depend solely on the field for which we define it over.
//! This interface allows us to have an easily swappable curve definition for different fields.
//!
//! Note that this would be cleaner if we could use trait specialization to keep the default
//! implementations in the trait itself, but this feature is not yet to that point of utility.

use super::*;
use crate::algebra::field::extension::PlutoExtensions;

/// The [`PlutoBaseCurve`] is an the base field set to the [`PlutoBaseField`]. This is the curve
/// used in the Pluto `ronkathon` system. The curve is defined by the equation `y^2 = x^3 + 3`.
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct PlutoBaseCurve;

/// The [`PlutoExtendedCurve`] is an instance of the same curve as the [`PlutoBaseCurve`], but with
/// field set to the [`PlutoBaseFieldExtension`].
///
/// This is the curve used in the Pluto `ronkathon`  system. The curve is defined by the equation
/// `y^2 = x^3 + 3`, but the field is extended to the quadratic extension field over the base field.
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct PlutoExtendedCurve;

impl EllipticCurve for PlutoBaseCurve {
  type BaseField = PlutoBaseField;
  type Coefficient = PlutoBaseField;
  type ScalarField = PlutoScalarField;

  const EQUATION_A: Self::Coefficient = PlutoBaseField::ZERO;
  const EQUATION_B: Self::Coefficient = PlutoBaseField::new(3);
  const GENERATOR: (Self::BaseField, Self::BaseField) =
    (PlutoBaseField::ONE, PlutoBaseField::new(2));
  const ORDER: usize = PlutoPrime::Scalar as usize;
}

impl EllipticCurve for PlutoExtendedCurve {
  type BaseField = PlutoBaseFieldExtension;
  type Coefficient = PlutoBaseField;
  type ScalarField = PlutoScalarField;

  const EQUATION_A: Self::Coefficient = PlutoBaseField::ZERO;
  const EQUATION_B: Self::Coefficient = PlutoBaseField::new(3);
  const GENERATOR: (Self::BaseField, Self::BaseField) = (
    PlutoBaseFieldExtension::new([PlutoBaseField::new(36), PlutoBaseField::ZERO]),
    PlutoBaseFieldExtension::new([PlutoBaseField::ZERO, PlutoBaseField::new(31)]),
  );
  const ORDER: usize = PlutoExtensions::QuadraticScalar as usize;
}

impl From<AffinePoint<PlutoBaseCurve>> for AffinePoint<PlutoExtendedCurve> {
  fn from(point: AffinePoint<PlutoBaseCurve>) -> Self {
    match point {
      AffinePoint::Point(x, y) => {
        let x = PlutoBaseFieldExtension::from(x);
        let y = PlutoBaseFieldExtension::from(y);
        AffinePoint::new(x, y)
      },
      AffinePoint::Infinity => AffinePoint::Infinity,
    }
  }
}

// TODO: have to remove const trait from finite field for this. Ask Colin or Waylon if that's
// alright
// impl<C: EllipticCurve> Distribution<AffinePoint<C>> for Standard {
//   #[inline]
//   fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> AffinePoint<C> {
//     loop {
//       let x = C::BaseField::rand(rng);
//       let rhs = x.pow(3) + x * C::EQUATION_A.into() + C::EQUATION_B.into();
//       if rhs.euler_criterion() {
//         if rand::random::<bool>() {
//           return AffinePoint::new(x, rhs.sqrt().unwrap().0);
//         } else {
//           return AffinePoint::new(x, rhs.sqrt().unwrap().1);
//         }
//       }
//     }
//   }
// }

#[cfg(test)]
mod pluto_base_curve_tests {
  use super::*;

  #[test]
  fn point_doubling() {
    let g = AffinePoint::<PlutoBaseCurve>::GENERATOR;

    let two_g = g.double();
    let expected_2g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(68), PlutoBaseField::new(74));
    let expected_negative_2g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(68), PlutoBaseField::new(27));
    assert_eq!(two_g, expected_2g);
    assert_eq!(-two_g, expected_negative_2g);

    let four_g = two_g.double();
    let expected_4g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(65), PlutoBaseField::new(98));
    let expected_negative_4g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(65), PlutoBaseField::new(3));
    assert_eq!(four_g, expected_4g);
    assert_eq!(-four_g, expected_negative_4g);

    let eight_g = four_g.double();
    let expected_8g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(18), PlutoBaseField::new(49));
    let expected_negative_8g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(18), PlutoBaseField::new(52));
    assert_eq!(eight_g, expected_8g);
    assert_eq!(-eight_g, expected_negative_8g);

    let sixteen_g = eight_g.double();
    let expected_16g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(1), PlutoBaseField::new(99));
    let expected_negative_16g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(1), PlutoBaseField::new(2));
    assert_eq!(sixteen_g, expected_16g);
    assert_eq!(-sixteen_g, expected_negative_16g);
    assert_eq!(g, -sixteen_g);
  }

  #[test]
  fn order_17() {
    let g: AffinePoint<PlutoBaseCurve> = AffinePoint::<PlutoBaseCurve>::GENERATOR;
    let mut g_double = g.double();
    let mut count = 2;
    while g_double != g && -g_double != g {
      g_double = g_double.double();
      count *= 2;
    }
    assert_eq!(count + 1, 17);
  }

  #[test]
  fn point_addition() {
    let g = AffinePoint::<PlutoBaseCurve>::GENERATOR;
    let two_g = g.double();
    let three_g = g + two_g;
    let expected_3g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(26), PlutoBaseField::new(45));
    let expected_negative_3g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(26), PlutoBaseField::new(56));
    assert_eq!(three_g, expected_3g);
    assert_eq!(-three_g, expected_negative_3g);

    let four_g = g + three_g;
    let expected_4g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(65), PlutoBaseField::new(98));
    let expected_negative_4g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(65), PlutoBaseField::new(3));
    assert_eq!(four_g, expected_4g);
    assert_eq!(-four_g, expected_negative_4g);

    let five_g = g + four_g;
    let expected_5g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(12), PlutoBaseField::new(32));
    let expected_negative_5g =
      AffinePoint::<PlutoBaseCurve>::new(PlutoBaseField::new(12), PlutoBaseField::new(69));
    assert_eq!(five_g, expected_5g);
    assert_eq!(-five_g, expected_negative_5g);

    assert_eq!(g + AffinePoint::Infinity, g);
    assert_eq!(AffinePoint::Infinity + g, g);
    assert_eq!(g + (-g), AffinePoint::Infinity);
  }

  #[test]
  fn scalar_multiplication_rhs() {
    let g = AffinePoint::<PlutoBaseCurve>::GENERATOR;
    let two_g = g * PlutoScalarField::new(2);
    let expected_2g: AffinePoint<PlutoBaseCurve> = g.double();
    assert_eq!(two_g, expected_2g);
    assert_eq!(-two_g, -expected_2g);
  }

  #[test]
  fn scalar_multiplication_lhs() {
    let g = AffinePoint::<PlutoBaseCurve>::GENERATOR;
    let two_g = 2 * g;
    let expected_2g = g.double();
    assert_eq!(two_g, expected_2g);
    assert_eq!(-two_g, -expected_2g);
  }
}

#[cfg(test)]
mod pluto_extended_curve_tests {
  use super::*;

  fn point() -> AffinePoint<PlutoExtendedCurve> {
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::new([PlutoBaseField::new(90), PlutoBaseField::ZERO]),
      PlutoBaseFieldExtension::new([PlutoBaseField::ZERO, PlutoBaseField::new(82)]),
    )
  }

  fn false_point() -> AffinePoint<PlutoExtendedCurve> {
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::new([PlutoBaseField::new(36), PlutoBaseField::ZERO]),
      PlutoBaseFieldExtension::new([PlutoBaseField::ZERO, PlutoBaseField::new(81)]),
    )
  }

  fn generator() -> AffinePoint<PlutoExtendedCurve> {
    AffinePoint::<PlutoExtendedCurve>::new(
      PlutoBaseFieldExtension::new([PlutoBaseField::new(36), PlutoBaseField::ZERO]),
      PlutoBaseFieldExtension::new([PlutoBaseField::ZERO, PlutoBaseField::new(31)]),
    )
  }

  #[rstest]
  #[case(AffinePoint::<PlutoExtendedCurve>::GENERATOR)]
  #[case(generator())]
  #[case(point())]
  #[should_panic]
  #[case(false_point())]
  fn on_curve(#[case] p: AffinePoint<PlutoExtendedCurve>) { let _ = p; }

  #[test]
  fn point_doubling() {
    let g = AffinePoint::<PlutoExtendedCurve>::GENERATOR;
    let two_g = g.double();

    let expected_g = generator();
    let expected_two_g = point();

    assert_eq!(two_g, expected_two_g);
    assert_eq!(g, expected_g);
  }

  #[test]
  fn scalar_multiplication_rhs() {
    let g = AffinePoint::<PlutoExtendedCurve>::GENERATOR;
    let two_g = g * PlutoScalarField::new(2);
    let expected_two_g = g.double();
    assert_eq!(two_g, expected_two_g);
    assert_eq!(-two_g, -expected_two_g);
  }

  #[test]
  fn scalar_multiplication_lhs() {
    let g = AffinePoint::<PlutoExtendedCurve>::GENERATOR;
    let two_g = 2 * g;
    let expected_two_g: AffinePoint<PlutoExtendedCurve> = g.double();
    assert_eq!(two_g, expected_two_g);
    assert_eq!(-two_g, -expected_two_g);
  }
}
