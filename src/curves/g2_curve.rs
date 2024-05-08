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



mod test {
    use crate::curves::AffinePoint;

    use super::*;

    #[test]
    fn doubling() {
        let g = AffinePoint::<G2Curve>::generator();
        println!("g: {:?}", g)

        // want to asset that g  = (36, 31*X)
        // want to asset that 2g = (90 , 82*X)
    }
}