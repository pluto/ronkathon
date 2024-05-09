use std::ops::Add;

use super::CurveParams;
use crate::field::{gf_101::GF101, gf_101_2::QuadraticPlutoField, ExtensionField, FiniteField};

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct G2Curve {}
// The Elliptic curve $y^2=x^3+3$, i.e.
// - a = 0
// - b = 3

impl CurveParams for  G2Curve {

    type FieldElement = QuadraticPlutoField<GF101>;

    const EQUATION_A: Self::FieldElement = QuadraticPlutoField::<GF101>::ZERO;
    const EQUATION_B: Self::FieldElement = QuadraticPlutoField::<GF101>::new(GF101::new(3), GF101::ZERO);
    const GENERATOR: (Self::FieldElement, Self::FieldElement) = (QuadraticPlutoField::<GF101>::new(GF101::new(36), GF101::ZERO), QuadraticPlutoField::<GF101>::new(GF101::ZERO, GF101::new(31)));
    const ORDER: u32 = 289; // extension field subgroup should have order r^2 where r is order of first group
    const THREE: QuadraticPlutoField<GF101> = QuadraticPlutoField::<GF101>::new(GF101::new(3), GF101::ZERO);
    const TWO: QuadraticPlutoField<GF101> = QuadraticPlutoField::<GF101>::new(GF101::TWO, GF101::ZERO);

}

// a naive impl with affine point

impl G2Curve {

    fn on_curve(x: QuadraticPlutoField<GF101>, y: QuadraticPlutoField<GF101>) -> (QuadraticPlutoField<GF101>, QuadraticPlutoField<GF101>) {
        println!("X: {:?}, Y: {:?}", x, y);
        // example: plug in (36 + 0x, 0 + 31x)
        // curve : y^2=x^3+3,
        // check if there are any x terms, if not, element is in base field
        let mut LHS = x * x * x;
        let mut RHS = y * y;
        if x.value[1] != GF101::ZERO {
            LHS = LHS * (-GF101::new(2)) - Self::EQUATION_B;
        } else {
            LHS = x * x * x - Self::EQUATION_B;
        }
        if y.value[1] != GF101::ZERO {
            // y has degree two so if there is a x -> there will be an x^2 term which we substitude with -2 since... 
            // TODO explain this and relationship to embedding degree
            RHS *= -GF101::new(2);
        } 
        LHS -= Self::EQUATION_B;
        assert_eq!(LHS, RHS, "Point is not on curve");
        (x, y)
    }
}






mod test {
    use crate::curves::AffinePoint;

    use super::*;

    #[test]
    fn doubling() {
        let g = AffinePoint::<G2Curve>::generator();
        println!("g: {:?}", g)

        // want to asset that g  = (36, 31*X)
        // right now this ^ fails to construct as it doesn't believe that the generator is a valid point on the curve
        // want to asset that 2g = (90 , 82*X)
    }
}