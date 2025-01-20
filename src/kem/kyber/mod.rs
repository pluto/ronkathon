use rand::Rng;

use crate::{
  algebra::field::prime::PrimeField,
  polynomial::{Basis, Monomial, Polynomial},
};

mod auxiliary;
mod compress;
mod encode;
mod kpke;
mod ntt;
mod sampling;
// #[cfg(test)] mod tests;

pub const MLKEM_Q: usize = 3329;
pub const MLKEM_N: usize = 256;

pub struct KPke<const K: usize> {
  pub eta1: usize,
  pub eta2: usize,
  pub du:   usize,
  pub dv:   usize,
}

pub type MlKemField = PrimeField<MLKEM_Q>;

pub struct Ntt;
impl Basis for Ntt {
  type Data = ();
}

pub type PolyRing<const D: usize> = Polynomial<Monomial, MlKemField, D>;
pub type NttPolyRing<const D: usize> = Polynomial<Ntt, MlKemField, D>;

pub struct PolyVec<B: Basis, const D: usize, const K: usize> {
  // TODO: might need to be written as [Polynomial<B, D>; K]
  pub vec: [Polynomial<B, MlKemField, D>; K],
}

impl<B: Basis, const D: usize, const K: usize> PolyVec<B, D, K> {
  pub fn new(vec: [Polynomial<B, MlKemField, D>; K]) -> Self { Self { vec } }
}

pub struct MatrixPolyVec<B: Basis, const D: usize, const K: usize> {
  pub vec: [PolyVec<B, D, K>; K],
}

// impl<const N: usize, const Q: usize, const K: usize> MatrixPolyVec<N, Q, K> {
//   pub fn new(vec: [PolyVec<N, Q, K>; K]) -> Self { Self { vec } }
// }

pub fn sample_ntt() -> Vec<u16> {
  let mut rng = rand::thread_rng();
  (0..256).map(|_| rng.gen_range(0..256)).collect()
}

impl<const K: usize> KPke<K> {
  pub fn new(eta1: usize, eta2: usize, du: usize, dv: usize) -> Self { Self { eta1, eta2, du, dv } }

  pub fn pke_keygen(&self, d: [u8; 32]) {
    // let (rho, sigma) = hash::g(&[d, [k]].concat());
    // let n = 0;
    // let mut a_ntt = Vec::with_capacity(capacity)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn poly_ring() {
    let coeffs = [MlKemField::new(1); 256];
    let poly: PolyRing<256> = PolyRing::new(coeffs);
  }
}
