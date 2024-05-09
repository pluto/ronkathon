use self::field::gf_101_2::Ext2;
use super::*;

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct G2Curve {}
// The Elliptic curve $y^2=x^3+3$, i.e.
// - a = 0
// - b = 3

impl CurveParams for G2Curve {
  type FieldElement = Ext2<GF101>;

  const EQUATION_A: Self::FieldElement = Ext2::<GF101>::ZERO;
  const EQUATION_B: Self::FieldElement = Ext2::<GF101>::new(GF101::new(3), GF101::ZERO);
  const GENERATOR: (Self::FieldElement, Self::FieldElement) = (
    Ext2::<GF101>::new(GF101::new(36), GF101::ZERO),
    Ext2::<GF101>::new(GF101::ZERO, GF101::new(31)),
  );
  const ORDER: u32 = 289;
  // extension field subgroup should have order r^2 where r is order of first group
  const THREE: Ext2<GF101> = Ext2::<GF101>::new(GF101::new(3), GF101::ZERO);
  const TWO: Ext2<GF101> = Ext2::<GF101>::new(GF101::TWO, GF101::ZERO);
}

// a naive impl with affine point

impl G2Curve {
  pub fn on_curve(x: Ext2<GF101>, y: Ext2<GF101>) -> (Ext2<GF101>, Ext2<GF101>) {
    println!("X: {:?}, Y: {:?}", x, y);
    // TODO Continue working on this
    //                  (   x  )  (  y   )  ( x , y )
    // example: plug in ((36, 0), (0, 31)): (36, 31t)
    // x = 36, y = 31t,
    // curve : y^2=x^3+3,

    // y = (31t)^2 = 52 * t^2
    // check if there are any x terms, if not, element is in base field
    let mut lhs = x;
    let mut rhs = y;
    if lhs.value[1] != GF101::ZERO {
      lhs = x * x * (-GF101::new(2)) - Self::EQUATION_B;
    } else {
      lhs = x * x * x - Self::EQUATION_B;
    }
    if y.value[1] != GF101::ZERO {
      // y has degree two so if there is a x -> there will be an x^2 term which we substitude with
      // -2 since... TODO explain this and relationship to embedding degree
      rhs *= -GF101::new(2);
    }
    // minus
    lhs -= Self::EQUATION_B;
    assert_eq!(lhs, rhs, "Point is not on curve");
    (x, y)
  }
}

mod tests {
  // use super::*;
  // use crate::curves::AffinePoint;

  // #[test]
  // fn on_curve() {
  //     let gen = G2Curve::on_curve(G2Curve::GENERATOR.0, G2Curve::GENERATOR.1);
  // }

  // #[test]
  // fn doubling() {
  //     let g = AffinePoint::<G2Curve>::generator();
  //     println!("g: {:?}", g)

  //     // want to asset that g  = (36, 31*X)
  //     // right now this ^ fails to construct as it doesn't believe that the generator is a valid
  // point on the curve     // want to asset that 2g = (90 , 82*X)
  // }
}
