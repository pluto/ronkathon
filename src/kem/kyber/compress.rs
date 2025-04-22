use super::{MlKemField, PolyVec};
use crate::{
  algebra::Finite,
  polynomial::{Monomial, Polynomial},
};

/// Compresses a number x to a number in the range [0, 2^d) using the formula round((2^d / q) * x)
/// mod 2^d.
/// round(a / b) = floor((a + b/2) / b)
pub fn compress_fieldelement<const d: usize>(x: &MlKemField) -> MlKemField {
  // TODO: Implement using barrett reduction
  let q_half = (MlKemField::ORDER + 1) >> 1;
  MlKemField::new((((x.value << d) + q_half) / MlKemField::ORDER) % (1 << d))
}

/// Decompresses a number y to a number in the range [0, q) using the formula round((q / 2^d)) * y.
pub fn decompress_fieldelement<const d: usize>(y: &MlKemField) -> MlKemField {
  let d_pow_half = 1 << (d - 1);
  let quotient = MlKemField::ORDER * y.value + d_pow_half;
  MlKemField::new(quotient >> d)
}

pub fn poly_compress<const D: usize, const d: usize>(
  poly: &Polynomial<Monomial, MlKemField, D>,
) -> Polynomial<Monomial, MlKemField, D> {
  // TODO: remove unwrap
  let coeffs = poly
    .coefficients
    .iter()
    .map(compress_fieldelement::<d>)
    .collect::<Vec<MlKemField>>()
    .try_into()
    .unwrap();

  Polynomial::<Monomial, MlKemField, D>::new(coeffs)
}

pub fn poly_decompress<const D: usize, const d: usize>(
  poly: &[MlKemField; D],
) -> Polynomial<Monomial, MlKemField, D> {
  let mut coefficients = [MlKemField::default(); D];
  for (i, x) in poly.iter().enumerate() {
    coefficients[i] = decompress_fieldelement::<d>(x);
  }
  Polynomial::<Monomial, MlKemField, D>::new(coefficients)
}

pub fn polyvec_compress<const D: usize, const d: usize, const K: usize>(
  poly_vec: &PolyVec<Monomial, D, K>,
) -> PolyVec<Monomial, D, K> {
  let mut res = Vec::with_capacity(K);

  for poly in poly_vec.vec.iter() {
    res.push(poly_compress::<D, d>(poly));
  }

  let res = res.try_into().unwrap();
  PolyVec::new(res)
}

pub fn polyvec_decompress<const D: usize, const d: usize, const K: usize>(
  poly_vec: &PolyVec<Monomial, D, K>,
) -> PolyVec<Monomial, D, K> {
  let mut res = Vec::with_capacity(K);

  for poly in poly_vec.vec.iter() {
    res.push(poly_decompress::<D, d>(&poly.coefficients));
  }

  let res = res.try_into().unwrap();
  PolyVec::new(res)
}

#[test]
fn test_compress_decompress() {
  let x = MlKemField::new(10);
  let z = decompress_fieldelement::<8>(&x);
  let y = compress_fieldelement::<8>(&z);
  assert_eq!(x, y);
}
