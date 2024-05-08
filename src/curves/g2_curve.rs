use std::ops::Add;
use crate::field::{gf_101::GF101, gf_101_2::QuadraticPlutoField, ExtensionField, FiniteField};
use super::CurveParams;


#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct G2Curve {}
// The Elliptic curve $y^2=x^3+3$, i.e.
// - a = 0
// - b = 3

impl CurveParams for G2Curve {
  type FieldElement = GF101;

  const EQUATION_A: Self::FieldElement = GF101::new(0);
  const EQUATION_B: Self::FieldElement = GF101::new(3);
  const GENERATOR: (Self::FieldElement, Self::FieldElement) = (GF101::new(36), GF101::new(31));
  const ORDER: u32 = Self::FieldElement::ORDER;
  const THREE: Self::FieldElement = GF101::new(3);
  const TWO: Self::FieldElement = GF101::new(2);
}

