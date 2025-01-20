use super::MlKemField;
use crate::{
  algebra::Finite,
  polynomial::{Monomial, Polynomial},
};

/// Compresses a number x to a number in the range [0, 2^d) using the formula round((2^d / q) * x)
/// mod 2^d.
/// round(a / b) = floor((a + b/2) / b)
pub fn compress_fieldelement<const D: usize>(x: &MlKemField) -> MlKemField {
  // TODO: Implement using barrett reduction
  let q_half = (MlKemField::ORDER + 1) >> 1;
  MlKemField::new((((x.value << D) + q_half) / MlKemField::ORDER) % (1 << D))
}

/// Decompresses a number y to a number in the range [0, q) using the formula round((q / 2^d)) * y.
pub fn decompress_fieldelement<const D: usize>(y: &MlKemField) -> MlKemField {
  let d_pow_half = 1 << (D - 1);
  let quotient = MlKemField::ORDER * y.value + d_pow_half;
  MlKemField::new(quotient >> D)
}

pub fn poly_compress<const D: usize>(
  poly: &Polynomial<Monomial, MlKemField, D>,
) -> [MlKemField; D] {
  // TODO: remove unwrap
  poly
    .coefficients
    .iter()
    .map(compress_fieldelement::<8>)
    .collect::<Vec<MlKemField>>()
    .try_into()
    .unwrap()
}

pub fn poly_decompress<const D: usize>(
  poly: &[MlKemField; D],
) -> Polynomial<Monomial, MlKemField, D> {
  let mut coefficients = [MlKemField::default(); D];
  for (i, x) in poly.iter().enumerate() {
    coefficients[i] = decompress_fieldelement::<8>(x);
  }
  Polynomial::<Monomial, MlKemField, D>::new(coefficients)
}

// pub fn polyvec_compress<const D: usize, const K: usize>(
//   poly_vec: &PolyVec<Monomial, D, K>,
// ) -> [[MlKemField; D]; K] {
//   let mut res = [[MlKemField::default(); D]; K];

//   for (i, poly) in poly_vec.vec.iter().enumerate() {
//     res[i] = poly_compress(poly);
//   }

//   res
// }

// pub fn polyvec_decompress<const D: usize, const K: usize>(

// )

#[test]
fn test_compress_decompress() {
  let x = MlKemField::new(10);
  let z = decompress_fieldelement::<8>(&x);
  let y = compress_fieldelement::<8>(&z);
  assert_eq!(x, y);
}
