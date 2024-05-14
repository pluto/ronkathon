//! This module contains the constants and methods for the Pluto curve over the prime field `GF101`
//! and its extensions.
//!
//! The basic idea here is that we have a curve that fixes `EQUATION_A` to 0 and `EQUATION_B` to 3.
//! The rest of the properties of the curve depend solely on the field for which we define it over.
//! This interface allows us to have an easily swappable curve definition for different fields.
//!
//! Note that this would be cleaner if we could use trait specialization to keep the default
//! implementations in the trait itself, but this feature is not yet to that point of utility.

use std::marker::PhantomData;

use super::*;

/// A struct that houses the constants and methods for the Pluto curve over the prime field `GF101`
/// and its extensions.
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct PlutoCurve<B: FiniteField> {
  _phantom: PhantomData<B>,
}

// TODO: It would be really nice if trait specialization could be used here to keep the default
// implementations in the trait itself, e.g., for the `EQUATION_A` and `EQUATION_B` constants.
impl EllipticCurve for PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>> {
  type BaseField = PrimeField<{ PlutoPrime::Base as usize }>;
  type Coefficient = PrimeField<{ PlutoPrime::Base as usize }>;

  const EQUATION_A: Self::Coefficient = PrimeField::<{ PlutoPrime::Base as usize }>::ZERO;
  const EQUATION_B: Self::Coefficient = PrimeField::<{ PlutoPrime::Base as usize }>::new(3);
  const GENERATOR: (Self::BaseField, Self::BaseField) = (
    PrimeField::<{ PlutoPrime::Base as usize }>::ONE,
    PrimeField::<{ PlutoPrime::Base as usize }>::TWO,
  );
  const ORDER: usize = PlutoPrime::Base as usize;
}

impl EllipticCurve for PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>> {
  type BaseField = GaloisField<2, { PlutoPrime::Base as usize }>;
  type Coefficient = PrimeField<{ PlutoPrime::Base as usize }>;

  const EQUATION_A: Self::Coefficient = PrimeField::<{ PlutoPrime::Base as usize }>::ZERO;
  const EQUATION_B: Self::Coefficient = PrimeField::<{ PlutoPrime::Base as usize }>::new(3);
  const GENERATOR: (Self::BaseField, Self::BaseField) = (
    GaloisField::<2, { PlutoPrime::Base as usize }>::new([
      PrimeField::<{ PlutoPrime::Base as usize }>::new(36),
      PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
    ]),
    GaloisField::<2, { PlutoPrime::Base as usize }>::new([
      PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
      PrimeField::<{ PlutoPrime::Base as usize }>::new(31),
    ]),
  );
  const ORDER: usize = PlutoExtensions::QuadraticBase as usize;
}

#[cfg(test)]
mod plut_curve_gf101_tests {
  use super::*;

  #[test]
  fn point_doubling() {
    let g = AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::generator();

    let two_g = g.point_doubling();
    let expected_2g = AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
      PrimeField::<{ PlutoPrime::Base as usize }>::new(68),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(74),
    );
    let expected_negative_2g =
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(68),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(27),
      );
    assert_eq!(two_g, expected_2g);
    assert_eq!(-two_g, expected_negative_2g);

    let four_g = two_g.point_doubling();
    let expected_4g = AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
      PrimeField::<{ PlutoPrime::Base as usize }>::new(65),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(98),
    );
    let expected_negative_4g =
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(65),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
      );
    assert_eq!(four_g, expected_4g);
    assert_eq!(-four_g, expected_negative_4g);

    let eight_g = four_g.point_doubling();
    let expected_8g = AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
      PrimeField::<{ PlutoPrime::Base as usize }>::new(18),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(49),
    );
    let expected_negative_8g =
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(18),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(52),
      );
    assert_eq!(eight_g, expected_8g);
    assert_eq!(-eight_g, expected_negative_8g);

    let sixteen_g = eight_g.point_doubling();
    let expected_16g = AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
      PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(99),
    );
    let expected_negative_16g =
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(1),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(2),
      );
    assert_eq!(sixteen_g, expected_16g);
    assert_eq!(-sixteen_g, expected_negative_16g);
    assert_eq!(g, -sixteen_g);
  }

  #[test]
  fn order_17() {
    let g = AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::generator();
    let mut g_double = g.point_doubling();
    let mut count = 2;
    while g_double != g && -g_double != g {
      g_double = g_double.point_doubling();
      count *= 2;
    }
    assert_eq!(count + 1, 17);
  }

  #[test]
  fn point_addition() {
    let g = AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::generator();
    let two_g = g.point_doubling();
    let three_g = g + two_g;
    let expected_3g = AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
      PrimeField::<{ PlutoPrime::Base as usize }>::new(26),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(45),
    );
    let expected_negative_3g =
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(26),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(56),
      );
    assert_eq!(three_g, expected_3g);
    assert_eq!(-three_g, expected_negative_3g);

    let four_g = g + three_g;
    let expected_4g = AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
      PrimeField::<{ PlutoPrime::Base as usize }>::new(65),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(98),
    );
    let expected_negative_4g =
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(65),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(3),
      );
    assert_eq!(four_g, expected_4g);
    assert_eq!(-four_g, expected_negative_4g);

    let five_g = g + four_g;
    let expected_5g = AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
      PrimeField::<{ PlutoPrime::Base as usize }>::new(12),
      PrimeField::<{ PlutoPrime::Base as usize }>::new(32),
    );
    let expected_negative_5g =
      AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::new(
        PrimeField::<{ PlutoPrime::Base as usize }>::new(12),
        PrimeField::<{ PlutoPrime::Base as usize }>::new(69),
      );
    assert_eq!(five_g, expected_5g);
    assert_eq!(-five_g, expected_negative_5g);

    assert_eq!(g + AffinePoint::Infinity, g);
    assert_eq!(AffinePoint::Infinity + g, g);
    assert_eq!(g + (-g), AffinePoint::Infinity);
  }

  #[test]
  fn scalar_multiplication_rhs() {
    let g = AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::generator();
    let two_g = g * 2;
    let expected_2g = g.point_doubling();
    assert_eq!(two_g, expected_2g);
    assert_eq!(-two_g, -expected_2g);
  }

  #[test]
  fn scalar_multiplication_lhs() {
    let g = AffinePoint::<PlutoCurve<PrimeField<{ PlutoPrime::Base as usize }>>>::generator();
    let two_g = 2 * g;
    let expected_2g = g.point_doubling();
    assert_eq!(two_g, expected_2g);
    assert_eq!(-two_g, -expected_2g);
  }
}

#[cfg(test)]
mod pluto_curve_ext2gf101_tests {
  use super::*;

  fn point() -> AffinePoint<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>> {
    AffinePoint::<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>>::new(
      GaloisField::<2, { PlutoPrime::Base as usize }>::new([
        PrimeField::<{ PlutoPrime::Base as usize }>::new(90),
        PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
      ]),
      GaloisField::<2, { PlutoPrime::Base as usize }>::new([
        PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
        PrimeField::<{ PlutoPrime::Base as usize }>::new(82),
      ]),
    )
  }

  fn false_point() -> AffinePoint<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>> {
    AffinePoint::<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>>::new(
      GaloisField::<2, { PlutoPrime::Base as usize }>::new([
        PrimeField::<{ PlutoPrime::Base as usize }>::new(36),
        PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
      ]),
      GaloisField::<2, { PlutoPrime::Base as usize }>::new([
        PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
        PrimeField::<{ PlutoPrime::Base as usize }>::new(81),
      ]),
    )
  }

  fn generator() -> AffinePoint<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>> {
    AffinePoint::<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>>::new(
      GaloisField::<2, { PlutoPrime::Base as usize }>::new([
        PrimeField::<{ PlutoPrime::Base as usize }>::new(36),
        PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
      ]),
      GaloisField::<2, { PlutoPrime::Base as usize }>::new([
        PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
        PrimeField::<{ PlutoPrime::Base as usize }>::new(31),
      ]),
    )
  }

  #[rstest]
  #[case(AffinePoint::<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>>::generator())]
  #[case(generator())]
  #[case(point())]
  #[should_panic]
  #[case(false_point())]
  fn on_curve(#[case] p: AffinePoint<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>>) {
    let _ = p;
  }

  #[test]
  fn point_doubling() {
    let g = AffinePoint::<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>>::generator();
    let two_g = g.point_doubling();

    let expected_g = generator();
    let expected_two_g = point();

    assert_eq!(two_g, expected_two_g);
    assert_eq!(g, expected_g);
  }

  #[test]
  fn scalar_multiplication_rhs() {
    let g = AffinePoint::<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>>::generator();
    let two_g = g * 2;
    let expected_two_g = g.point_doubling();
    assert_eq!(two_g, expected_two_g);
    assert_eq!(-two_g, -expected_two_g);
  }

  #[test]
  fn scalar_multiplication_lhs() {
    let g = AffinePoint::<PlutoCurve<GaloisField<2, { PlutoPrime::Base as usize }>>>::generator();
    let two_g = 2 * g;
    let expected_two_g = g.point_doubling();
    assert_eq!(two_g, expected_two_g);
    assert_eq!(-two_g, -expected_two_g);
  }
}
