use super::*;

/// The Elliptic curve $y^2=x^3+3$, i.e.
/// - a = 0
/// - b = 3
/// - generator todo
/// - order todo
/// - field element type todo, but mock with u64 - bad thor, u64 does not implement p3_field
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct C101;

impl CurveParams for C101 {
  type FieldElement = GF101;

  const EQUATION_A: Self::FieldElement = GF101::new(0);
  const EQUATION_B: Self::FieldElement = GF101::new(3);
  const GENERATOR: (Self::FieldElement, Self::FieldElement) = (GF101::new(1), Self::TWO);
  const ORDER: u32 = GF101::ORDER;
  const THREE: Self::FieldElement = GF101::new(3);
  const TWO: Self::FieldElement = GF101::new(2);
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn point_doubling() {
    let g = AffinePoint::<C101>::generator();

    let two_g = g.point_doubling();
    let expected_2g = AffinePoint::<C101>::new(GF101::new(68), GF101::new(74));
    let expected_negative_2g = AffinePoint::<C101>::new(GF101::new(68), GF101::new(27));
    assert_eq!(two_g, expected_2g);
    assert_eq!(-two_g, expected_negative_2g);

    let four_g = two_g.point_doubling();
    let expected_4g = AffinePoint::<C101>::new(GF101::new(65), GF101::new(98));
    let expected_negative_4g = AffinePoint::<C101>::new(GF101::new(65), GF101::new(3));
    assert_eq!(four_g, expected_4g);
    assert_eq!(-four_g, expected_negative_4g);

    let eight_g = four_g.point_doubling();
    let expected_8g = AffinePoint::<C101>::new(GF101::new(18), GF101::new(49));
    let expected_negative_8g = AffinePoint::<C101>::new(GF101::new(18), GF101::new(52));
    assert_eq!(eight_g, expected_8g);
    assert_eq!(-eight_g, expected_negative_8g);

    let sixteen_g = eight_g.point_doubling();
    let expected_16g = AffinePoint::<C101>::new(GF101::new(1), GF101::new(99));
    let expected_negative_16g = AffinePoint::<C101>::new(GF101::new(1), GF101::new(2));
    assert_eq!(sixteen_g, expected_16g);
    assert_eq!(-sixteen_g, expected_negative_16g);
    assert_eq!(g, -sixteen_g);
  }

  #[test]
  fn order_17() {
    let g = AffinePoint::<C101>::generator();
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
    let g = AffinePoint::<C101>::generator();
    let two_g = g.point_doubling();
    let three_g = g + two_g;
    let expected_3g = AffinePoint::<C101>::new(GF101::new(26), GF101::new(45));
    let expected_negative_3g = AffinePoint::<C101>::new(GF101::new(26), GF101::new(56));
    assert_eq!(three_g, expected_3g);
    assert_eq!(-three_g, expected_negative_3g);

    let four_g = g + three_g;
    let expected_4g = AffinePoint::<C101>::new(GF101::new(65), GF101::new(98));
    let expected_negative_4g = AffinePoint::<C101>::new(GF101::new(65), GF101::new(3));
    assert_eq!(four_g, expected_4g);
    assert_eq!(-four_g, expected_negative_4g);

    let five_g = g + four_g;
    let expected_5g = AffinePoint::<C101>::new(GF101::new(12), GF101::new(32));
    let expected_negative_5g = AffinePoint::<C101>::new(GF101::new(12), GF101::new(69));
    assert_eq!(five_g, expected_5g);
    assert_eq!(-five_g, expected_negative_5g);

    assert_eq!(g + AffinePoint::new_infty(), g);
    assert_eq!(AffinePoint::new_infty() + g, g);
    assert_eq!(g + (-g), AffinePoint::new_infty());
  }

  #[test]
  fn scalar_multiplication_rhs() {
    let g = AffinePoint::<C101>::generator();
    let two_g = g * 2;
    let expected_2g = g.point_doubling();
    assert_eq!(two_g, expected_2g);
    assert_eq!(-two_g, -expected_2g);
  }

  #[test]
  fn scalar_multiplication_lhs() {
    let g = AffinePoint::<C101>::generator();
    let two_g = 2 * g;
    let expected_2g = g.point_doubling();
    assert_eq!(two_g, expected_2g);
    assert_eq!(-two_g, -expected_2g);
  }
}
