use std::ops::Add;

use super::CurveParams;
use crate::field::{gf_101::GF101, gf_101_2::QuadraticPlutoField, ExtensionField, FiniteField};

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct G2Curve {}
// The Elliptic curve $y^2=x^3+3$, i.e.
// - a = 0
// - b = 3

impl CurveParams for G2Curve {
  type FieldElement = QuadraticPlutoField<GF101>;

  const EQUATION_A: Self::FieldElement = QuadraticPlutoField::<GF101>::ZERO;
  const EQUATION_B: Self::FieldElement =
    QuadraticPlutoField::<GF101>::new(GF101::new(3), GF101::ZERO);
  const GENERATOR: (Self::FieldElement, Self::FieldElement) = (
    QuadraticPlutoField::<GF101>::new(GF101::new(36), GF101::ZERO),
    QuadraticPlutoField::<GF101>::new(GF101::ZERO, GF101::new(31)),
  );
  const ORDER: u32 = 289;
  // extension field subgroup should have order r^2 where r is order of first group
  const THREE: QuadraticPlutoField<GF101> =
    QuadraticPlutoField::<GF101>::new(GF101::new(3), GF101::ZERO);
  const TWO: QuadraticPlutoField<GF101> =
    QuadraticPlutoField::<GF101>::new(GF101::TWO, GF101::ZERO);
}

// a naive impl with affine point

impl G2Curve {
  pub fn on_curve(
    x: QuadraticPlutoField<GF101>,
    y: QuadraticPlutoField<GF101>,
  ) -> Option<(QuadraticPlutoField<GF101>, QuadraticPlutoField<GF101>)> {
    println!("X: {:?}, Y: {:?}", x, y);
    //                  (   x  )  (  y   )  ( x , y )
    // example: plug in ((36, 0), (0, 31)): (36, 31t)
    // x = 36, y = 31t,
    // curve : y^2=x^3+3,

    // Compute x^3 considering t^2 = -2
    let x_cubed = if x.value[1] != GF101::ZERO {
      let x_squared = QuadraticPlutoField::<GF101>::new(
          x.value[0] * x.value[0] - GF101::TWO * x.value[1] * x.value[1], // a^2 - 2b^2
          GF101::TWO * x.value[0] * x.value[1] // 2ab
      );
      QuadraticPlutoField::<GF101>::new(
          x_squared.value[0] * x.value[0] - GF101::TWO * x_squared.value[1] * x.value[1], // a^2 - 2b^2
          x_squared.value[0] * x.value[1] + x_squared.value[1] * x.value[0] // ab + ba
      )
    } else {
        QuadraticPlutoField::<GF101>::new(x.value[0] * x.value[0] * x.value[0], GF101::ZERO) // a^3
    };

    // Compute y^2 considering t^2 = -2
    let y_squared = if y.value[1] != GF101::ZERO {
        QuadraticPlutoField::<GF101>::new(
            y.value[0] * y.value[0] - GF101::TWO * y.value[1] * y.value[1], // a^2 - 2b^2
            GF101::TWO * y.value[0] * y.value[1] // 2ab
        )
    } else {
        QuadraticPlutoField::<GF101>::new(y.value[0] * y.value[0], GF101::ZERO) // a^2
    };

    // Add the constant term from the curve equation y^2 = x^3 + 3
    let x_cubed_plus_b = x_cubed + Self::EQUATION_B;

    // Check if the point satisfies the curve equation
    let is_on_curve = y_squared == x_cubed_plus_b;

    if is_on_curve {
        println!("The point ({:?}, {:?}) is on the curve.", x, y);
        Some((x, y))
    } else {
        println!("The point ({:?}, {:?}) is not on the curve.", x, y);
        None
    }
  }
}

mod test {
  use super::*;
  use crate::curves::AffinePoint;

  #[test]
  fn on_curve() {
      let gen = G2Curve::on_curve(G2Curve::GENERATOR.0, G2Curve::GENERATOR.1);
  }
}