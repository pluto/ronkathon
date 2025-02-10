use std::ops::Mul;

use super::{MlKemField, Ntt, PolyVec};
use crate::{
  algebra::{field::Field, Finite},
  polynomial::{Monomial, Polynomial},
};

const ZETA: usize = 17;
const fn bitrev_7(x: usize) -> usize {
  (x >> 6) & 1
    | ((x >> 5) & 1) << 1
    | ((x >> 4) & 1) << 2
    | ((x >> 3) & 1) << 3
    | ((x >> 2) & 1) << 4
    | ((x >> 1) & 1) << 5
    | (x & 1) << 6
}

const ZETA_POW: [MlKemField; 128] = {
  let mut i = 0;
  let mut curr = 1;
  let mut zeta_pow = [MlKemField::ZERO; 128];
  while i < 128 {
    zeta_pow[i] = MlKemField::new(curr);
    curr = curr * ZETA % MlKemField::ORDER;
    i += 1;
  }

  let mut zeta_pow_rev = [MlKemField::ZERO; 128];
  let mut i = 0;
  while i < 128 {
    zeta_pow_rev[i] = zeta_pow[bitrev_7(i)];
    i += 1;
  }

  zeta_pow_rev
};

const GAMMA: [MlKemField; 128] = {
  let mut gamma = [MlKemField::ZERO; 128];
  let mut i = 0;
  while i < 128 {
    gamma[i] =
      MlKemField { value: (ZETA_POW[i].value * ZETA_POW[i].value * ZETA) % MlKemField::ORDER };
    i += 1;
  }

  gamma
};

impl<const D: usize> Polynomial<Monomial, MlKemField, D> {
  pub fn ntt(self) -> Polynomial<Ntt, MlKemField, D> {
    let mut f_ntt_coeffs = [MlKemField::ZERO; D];
    let mut i = 1;
    let mut len = 128;
    while len >= 2 {
      for start in (0..256).step_by(len * 2) {
        let zeta = ZETA_POW[i];
        i += 1;
        for j in start..start + len {
          let t = zeta * self.coefficients[j + len];
          f_ntt_coeffs[j + len] = self.coefficients[j] - t;
          f_ntt_coeffs[j] = self.coefficients[j] + t;
        }
      }
      len >>= 1;
    }

    Polynomial::<Ntt, MlKemField, D> { coefficients: f_ntt_coeffs, basis: Ntt }
  }
}

impl<const D: usize, const K: usize> PolyVec<Monomial, D, K> {
  pub fn ntt(self) -> PolyVec<Ntt, D, K> {
    let ntt_vec = self.vec.iter().map(|poly| poly.ntt()).collect::<Vec<_>>().try_into().unwrap();

    PolyVec::<Ntt, D, K> { vec: ntt_vec }
  }
}

impl<const D: usize, const K: usize> PolyVec<Ntt, D, K> {
  pub fn ntt_inv(self) -> PolyVec<Monomial, D, K> {
    let ntt_inv_vec =
      self.vec.iter().map(|poly| poly.ntt_inv()).collect::<Vec<_>>().try_into().unwrap();

    PolyVec { vec: ntt_inv_vec }
  }
}

impl<const D: usize> Mul<&Polynomial<Ntt, MlKemField, D>> for &Polynomial<Ntt, MlKemField, D> {
  type Output = Polynomial<Ntt, MlKemField, D>;

  fn mul(self, rhs: &Polynomial<Ntt, MlKemField, D>) -> Self::Output {
    let mut res_coeffs = [MlKemField::ZERO; D];

    for i in 0..D >> 1 {
      let (a0, a1) = (self.coefficients[2 * i], self.coefficients[2 * i + 1]);
      let (b0, b1) = (rhs.coefficients[2 * i], rhs.coefficients[2 * i + 1]);
      let (c0, c1) = (a0 * b0 + GAMMA[i] * a1 * b1, a0 * b1 + a1 * b0);
      res_coeffs[2 * i] = c0;
      res_coeffs[2 * i + 1] = c1;
    }

    Polynomial::<Ntt, MlKemField, D> { coefficients: res_coeffs, basis: Ntt }
  }
}

impl<const D: usize> Polynomial<Ntt, MlKemField, D> {
  pub fn ntt_inv(self) -> Polynomial<Monomial, MlKemField, D> {
    let mut f_coeffs = [MlKemField::ZERO; D];
    let mut i = 127;
    let mut len = 2;
    while len <= 128 {
      for start in (0..256).step_by(2 * len) {
        let zeta = ZETA_POW[i];
        i -= 1;
        for j in start..start + len {
          let t = self.coefficients[j];
          f_coeffs[j] = t + self.coefficients[j + len];
          f_coeffs[j + len] = zeta * (self.coefficients[j + len] - t);
        }
      }
      len <<= 1;
    }

    Polynomial::<Monomial, MlKemField, D> { coefficients: f_coeffs, basis: Monomial }
  }
}
