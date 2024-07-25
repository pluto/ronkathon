use crate::algebra::field::{
  prime::{find_primitive_element, PrimeField},
  FiniteField,
};

// /// [`FiniteGroup`] under multiplication implemented as integer, $Z/rZ$ modulo prime `r`.
// #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
// pub struct MultiplicativePrimeGroup<const P: usize>(usize);

// impl<const P: usize> FiniteGroup for MultiplicativePrimeGroup<P> {
//   type Scalar = PrimeField<P>;

//   const GENERATOR: Self = Self(find_primitive_element::<P>());
//   const IDENTITY: Self = Self(1);
//   const ORDER: usize = P;

//   fn operation(a: &Self, b: &Self) -> Self { Self(a.0 * b.0 % Self::ORDER) }

//   fn inverse(&self) -> Self { self.scalar_mul(&Self::Scalar::new(Self::ORDER - 2)) }

//   fn scalar_mul(&self, b: &Self::Scalar) -> Self {
//     let mut res = Self(1);
//     for _ in 0..b.value {
//       res = Self::operation(&res, self);
//     }
//     res
//   }
// }

// impl<const P: usize> Add for MultiplicativePrimeGroup<P> {
//   type Output = Self;

//   fn add(self, rhs: Self) -> Self::Output { Self::operation(&self, &rhs) }
// }

// impl<const P: usize> AddAssign for MultiplicativePrimeGroup<P> {
//   fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
// }

// impl<const P: usize> Neg for MultiplicativePrimeGroup<P> {
//   type Output = Self;

//   fn neg(self) -> Self::Output { Self::inverse(&self) }
// }

// impl<const P: usize> Sub for MultiplicativePrimeGroup<P> {
//   type Output = Self;

//   fn sub(self, rhs: Self) -> Self::Output { self + -rhs }
// }

// impl<const P: usize> SubAssign for MultiplicativePrimeGroup<P> {
//   fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
// }

// impl<const P: usize> Mul<PrimeField<P>> for MultiplicativePrimeGroup<P> {
//   type Output = Self;

//   fn mul(self, rhs: PrimeField<P>) -> Self::Output { Self::scalar_mul(&self, &rhs) }
// }

// impl<const P: usize> MulAssign<PrimeField<P>> for MultiplicativePrimeGroup<P> {
//   fn mul_assign(&mut self, rhs: PrimeField<P>) { *self = *self * rhs; }
// }

// #[cfg(test)]
// mod tests {
//   use super::*;

//   #[test]
//   fn mul_group_properties() {
//     type MulGroup = MultiplicativePrimeGroup<17>;
//     type ScalarField = PrimeField<17>;

//     let gen = MultiplicativePrimeGroup::<17>::GENERATOR;

//     let ident = MulGroup::IDENTITY;

//     // commutativity
//     assert_eq!(gen + ident, ident + gen);
//     // inverse
//     assert_eq!(gen + gen.inverse(), ident);
//     // associativity
//     assert_eq!(gen + (ident + gen), (gen + gen) + ident);
//     // scalar multiplication
//     assert_eq!(gen * ScalarField::new(2), gen + gen);
//   }
// }
