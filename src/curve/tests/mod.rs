use std::array;

use self::field::extension::ExtensionField;
use super::*;

mod fields;
use fields::*;

// Let's work through the example in Lynn's thesis so that we can be sure we compute the Tate
// pairing correctly.

// The curve is given by E: y^2 = x^3 + x over F_59.
// The curve has 60 points and we will take r = 5 to get a group in the 5-torsion called G.
// One generator for this group is P = (25,30) and we get:
// G = {P, 2P, 3P, 4P, 5p } = {(25,30), (35,31), (35,28), (25,29), O}

// We extend F_59 to F_59^2 by adjoining a root of t^2 + 1 = 0.s
// Then we will need the distortion map: (x,y) -> (-x, iy) where i^2 = -1. (See `fields` module
// below)

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
struct TestCurve;

impl EllipticCurve for TestCurve {
  type BaseField = TestField;
  type Coefficient = TestField;

  const EQUATION_A: Self::Coefficient = TestField::ONE;
  const EQUATION_B: Self::Coefficient = TestField::ZERO;
  // In this case, this isn't really the generator for the curve, but rather the generator for the
  // 5-torsion subgroup.
  const GENERATOR: (Self::BaseField, Self::BaseField) = (TestField::new(25), TestField::new(30));
  const ORDER: usize = 5;
}

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
struct TestCurveExtended;

impl EllipticCurve for TestCurveExtended {
  type BaseField = TestExtension;
  type Coefficient = TestField;

  const EQUATION_A: Self::Coefficient = TestField::ONE;
  const EQUATION_B: Self::Coefficient = TestField::ZERO;
  const GENERATOR: (Self::BaseField, Self::BaseField) =
    (TestExtension::from(25_usize), TestExtension::from(30_usize));
  const ORDER: usize = 5;
}

#[test]
fn five_torsion() {
  let generator = AffinePoint::<TestCurve>::generator();
  println!("Generator: {:?}", generator);
  for i in 1..6 {
    let point = generator * i as u32;
    println!("{:?} * P = {:?}", i, point);
    if i == 5 {
      assert_eq!(point, AffinePoint::Infinity);

      continue;
    } else {
      assert!(point != AffinePoint::Infinity);
    }
  }
  // We should get:
  // 1 * P = Point(PrimeField { value: 25 }, PrimeField { value: 30 })
  // 2 * P = Point(PrimeField { value: 35 }, PrimeField { value: 31 })
  // 3 * P = Point(PrimeField { value: 35 }, PrimeField { value: 28 })
  // 4 * P = Point(PrimeField { value: 25 }, PrimeField { value: 29 })
  // 5 * P = Infinity
  println!("\n\n");

  let torsion_generator =
    if let AffinePoint::<TestCurve>::Point(x, y) = AffinePoint::<TestCurve>::generator() {
      // Apply the distortion map
      AffinePoint::<TestCurveExtended>::new(
        -TestExtension::from(x),
        TestExtension::new([TestField::from(0usize), TestField::from(1usize)])
          * TestExtension::from(y),
      )
    } else {
      panic!("Generator is not a point");
    };

  println!("Distortion map on generator: {:?}", torsion_generator);
  for i in 1..6 {
    let point = torsion_generator * i as u32;
    println!("{:?} * P = {:?}", i, point);
    if i == 5 {
      assert_eq!(point, AffinePoint::Infinity);

      continue;
    } else {
      assert!(point != AffinePoint::Infinity);
    }
  }
}
