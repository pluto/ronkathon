use std::ops::{Add, AddAssign, Mul};

use auxiliary::{g, h};
use compress::{poly_compress, poly_decompress, polyvec_compress, polyvec_decompress};
use encode::{byte_decode, byte_decode_polyvec, byte_encode, byte_encode_polyvec};
use rand::Rng;

use crate::{
  algebra::field::prime::PrimeField,
  polynomial::{Basis, Monomial, Polynomial},
};

mod auxiliary;
mod compress;
mod encode;
// mod kpke;
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

#[derive(Debug, Clone, Copy)]
pub struct Ntt;
impl Basis for Ntt {
  type Data = ();
}

pub type PolyRing<const D: usize> = Polynomial<Monomial, MlKemField, D>;
pub type NttPolyRing<const D: usize> = Polynomial<Ntt, MlKemField, D>;

impl<const D: usize> Add for &NttPolyRing<D> {
  type Output = NttPolyRing<D>;

  fn add(self, rhs: Self) -> Self::Output {
    let coeffs = self
      .coefficients
      .iter()
      .zip(rhs.coefficients.iter())
      .map(|(&a, &b)| a + b)
      .collect::<Vec<MlKemField>>()
      .try_into()
      .unwrap();
    NttPolyRing::new(coeffs)
  }
}

impl<const D: usize> AddAssign for NttPolyRing<D> {
  fn add_assign(&mut self, rhs: Self) {
    for i in 0..D {
      self.coefficients[i] += rhs.coefficients[i];
    }
  }
}

impl<const D: usize> NttPolyRing<D> {
  pub fn new(coeffs: [MlKemField; D]) -> Self { Self { coefficients: coeffs, basis: Ntt } }
}

#[derive(Debug, Clone, Copy)]
pub struct PolyVec<B: Basis, const D: usize, const K: usize> {
  // TODO: might need to be written as [Polynomial<B, D>; K]
  pub vec: [Polynomial<B, MlKemField, D>; K],
}

impl<B: Basis, const D: usize, const K: usize> PolyVec<B, D, K> {
  pub fn new(vec: [Polynomial<B, MlKemField, D>; K]) -> Self { Self { vec } }
}

impl<const D: usize, const K: usize> PolyVec<Ntt, D, K> {
  pub fn dot_product(&self, rhs: &Self) -> NttPolyRing<D> {
    let mut result = NttPolyRing::new([MlKemField::ZERO; D]);
    for i in 0..K {
      result += &self.vec[i] * &rhs.vec[i];
    }
    result
  }
}

impl<const D: usize, const K: usize> Add for PolyVec<Ntt, D, K> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    let vec = (0..K)
      .map(|i| &self.vec[i] + &rhs.vec[i])
      .collect::<Vec<Polynomial<Ntt, MlKemField, D>>>()
      .try_into()
      .unwrap();
    Self::new(vec)
  }
}

impl<const D: usize, const K: usize> Add for PolyVec<Monomial, D, K> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    let vec = (0..K)
      .map(|i| self.vec[i] + rhs.vec[i])
      .collect::<Vec<Polynomial<Monomial, MlKemField, D>>>()
      .try_into()
      .unwrap();
    Self::new(vec)
  }
}

// impl<B: Basis, const D: usize, const K: usize> Iterator for PolyVec<B, D, K> {
//   type Item = Polynomial<B, MlKemField, D>;

//   fn next(&mut self) -> Option<Self::Item> { self.vec.iter().next().copied() }
// }

/// A matrix of polynomial vectors of size K \times K.
pub struct MatrixPolyVec<B: Basis, const D: usize, const K: usize> {
  pub vec: [PolyVec<B, D, K>; K],
}

impl<B: Basis, const D: usize, const K: usize> MatrixPolyVec<B, D, K> {
  /// Creates a new matrix of polynomial vectors.
  pub fn new(vec: [PolyVec<B, D, K>; K]) -> Self { Self { vec } }
}

impl<B: Basis, const D: usize, const K: usize> MatrixPolyVec<B, D, K> {
  pub fn transpose(&self) -> Self {
    let poly_vec = (0..K)
      .map(|col_idx| {
        let vec = (0..K)
          .map(|row_idx| self.vec[row_idx].vec[col_idx].clone())
          .collect::<Vec<Polynomial<B, MlKemField, D>>>()
          .try_into()
          .unwrap();
        PolyVec::new(vec)
      })
      .collect::<Vec<PolyVec<B, D, K>>>()
      .try_into()
      .unwrap();

    Self::new(poly_vec)
  }
}

use crate::algebra::field::Field;

impl<const D: usize, const K: usize> Mul<&PolyVec<Ntt, D, K>> for MatrixPolyVec<Ntt, D, K> {
  type Output = PolyVec<Ntt, D, K>;

  fn mul(self, rhs: &PolyVec<Ntt, D, K>) -> Self::Output {
    let res = (0..K)
      .map(|i| {
        let mut sum = NttPolyRing::new([MlKemField::ZERO; D]);
        for j in 0..K {
          sum += &self.vec[i].vec[j] * &rhs.vec[j];
        }
        sum
      })
      .collect::<Vec<NttPolyRing<D>>>()
      .try_into()
      .unwrap();

    PolyVec::new(res)
  }
}

pub struct KPkeEncryptionKey<const K: usize>([u8; 384 * K + 32])
where [(); 384 * K + 32]:;
pub struct KPkeDecryptionKey<const K: usize>([u8; 384 * K])
where [(); 384 * K]:;

impl<const K: usize> KPke<K> {
  pub fn new(eta1: usize, eta2: usize, du: usize, dv: usize) -> Self { Self { eta1, eta2, du, dv } }

  pub fn pke_keygen<const eta1: usize>(
    &self,
    d: [u8; 32],
  ) -> (KPkeEncryptionKey<K>, KPkeDecryptionKey<K>)
  where
    [(); 64 * eta1]:,
    [(); 64 * eta1 * 8]:,
    [(); 384 * K + 32]:,
    [(); 384 * K]:,
  {
    let mut input = d.to_vec();
    input.push(K as u8);
    let (rho, sigma) = auxiliary::g(&input);

    let mut n = 0;

    let a_hat_vec: [PolyVec<Ntt, MLKEM_N, K>; K] = (0..K)
      .map(|i| {
        let vec: [NttPolyRing<MLKEM_N>; K] = (0..K)
          .map(|j| {
            let coeffs = sampling::sample_ntt(&rho, j as u8, i as u8);
            NttPolyRing::new(coeffs)
          })
          .collect::<Vec<NttPolyRing<MLKEM_N>>>()
          .try_into()
          .unwrap();
        PolyVec::new(vec)
      })
      .collect::<Vec<PolyVec<Ntt, MLKEM_N, K>>>()
      .try_into()
      .unwrap();
    let a_hat: MatrixPolyVec<Ntt, MLKEM_N, K> = MatrixPolyVec::new(a_hat_vec);

    let vec: [PolyRing<MLKEM_N>; K] = (0..K)
      .map(|_| {
        let seed = auxiliary::prf::<eta1>(&sigma, n);
        n += 1;
        let coeffs = sampling::sample_poly_cbd::<eta1>(seed);
        PolyRing::new(coeffs)
      })
      .collect::<Vec<PolyRing<MLKEM_N>>>()
      .try_into()
      .unwrap();
    let s: PolyVec<Monomial, MLKEM_N, K> = PolyVec::new(vec);

    let vec: [PolyRing<MLKEM_N>; K] = (0..K)
      .map(|_| {
        let seed = auxiliary::prf::<eta1>(&sigma, n);
        n += 1;
        let coeffs = sampling::sample_poly_cbd::<eta1>(seed);
        PolyRing::new(coeffs)
      })
      .collect::<Vec<PolyRing<MLKEM_N>>>()
      .try_into()
      .unwrap();
    let e: PolyVec<Monomial, MLKEM_N, K> = PolyVec::new(vec);

    let s_hat = s.ntt();
    let e_hat = e.ntt();

    let t_hat = a_hat * &s_hat + e_hat;

    let ek = [byte_encode_polyvec::<Ntt, MLKEM_N, K, 12>(t_hat), rho.to_vec()]
      .concat()
      .try_into()
      .unwrap();
    let dk = byte_encode_polyvec::<Ntt, MLKEM_N, K, 12>(s_hat).try_into().unwrap();

    (KPkeEncryptionKey(ek), KPkeDecryptionKey(dk))
  }

  pub fn kpke_encrypt<const eta1: usize, const eta2: usize, const du: usize, const dv: usize>(
    &self,
    encryption_key: KPkeEncryptionKey<K>,
    m: [u8; 32],
    r: [u8; 32],
  ) -> Vec<u8>
  where
    [(); 384 * K + 32]:,
    [(); 64 * eta1]:,
    [(); 64 * eta1 * 8]:,
    [(); 64 * eta2]:,
    [(); 64 * eta2 * 8]:,
  {
    let mut n = 0;
    let (t_hat, rho) = encryption_key.0.split_at(384 * K);
    let t_hat = byte_decode_polyvec::<Ntt, MLKEM_N, K, 12>(t_hat, Ntt);
    let rho: [u8; 32] = rho.try_into().unwrap();

    let a_hat_vec: [PolyVec<Ntt, MLKEM_N, K>; K] = (0..K)
      .map(|i| {
        let vec: [NttPolyRing<MLKEM_N>; K] = (0..K)
          .map(|j| {
            let coeffs = sampling::sample_ntt(&rho, j as u8, i as u8);
            NttPolyRing::new(coeffs)
          })
          .collect::<Vec<NttPolyRing<MLKEM_N>>>()
          .try_into()
          .unwrap();
        PolyVec::new(vec)
      })
      .collect::<Vec<PolyVec<Ntt, MLKEM_N, K>>>()
      .try_into()
      .unwrap();
    let a_hat: MatrixPolyVec<Ntt, MLKEM_N, K> = MatrixPolyVec::new(a_hat_vec);

    let vec: [PolyRing<MLKEM_N>; K] = (0..K)
      .map(|_| {
        let seed = auxiliary::prf::<eta1>(&r, n);
        n += 1;
        let coeffs = sampling::sample_poly_cbd::<eta1>(seed);
        PolyRing::new(coeffs)
      })
      .collect::<Vec<PolyRing<MLKEM_N>>>()
      .try_into()
      .unwrap();
    let y: PolyVec<Monomial, MLKEM_N, K> = PolyVec::new(vec);

    let vec: [PolyRing<MLKEM_N>; K] = (0..K)
      .map(|_| {
        let seed = auxiliary::prf::<eta2>(&r, n);
        n += 1;
        let coeffs = sampling::sample_poly_cbd::<eta2>(seed);
        PolyRing::new(coeffs)
      })
      .collect::<Vec<PolyRing<MLKEM_N>>>()
      .try_into()
      .unwrap();
    let e1: PolyVec<Monomial, MLKEM_N, K> = PolyVec::new(vec);

    let e2 = PolyRing::new(sampling::sample_poly_cbd::<eta2>(auxiliary::prf::<eta2>(&r, n)));

    let y_hat = y.ntt();

    let u = (a_hat.transpose() * &y_hat).ntt_inv() + e1;

    let mu = poly_decompress::<MLKEM_N, 1>(&byte_decode::<1, MLKEM_N>(&m));

    let v = t_hat.dot_product(&y_hat).ntt_inv() + e2 + mu;
    // let c1 = poly_compress::<MLKEM_N, du>(&u);
    let c1_compressed = polyvec_compress::<MLKEM_N, du, K>(&u);
    let c1 = byte_encode_polyvec::<Monomial, MLKEM_N, K, du>(c1_compressed);
    let c2_compressed = poly_compress::<MLKEM_N, dv>(&v);
    let c2 = byte_encode::<dv, MLKEM_N>(&c2_compressed.coefficients);
    [c1, c2].concat()
  }

  pub fn kpke_decrypt<const eta1: usize, const eta2: usize, const du: usize, const dv: usize>(
    &self,
    decryption_key: KPkeDecryptionKey<K>,
    c: Vec<u8>,
  ) -> [u8; 32]
  where
    [(); 384 * K]:,
    [(); 64 * eta1]:,
    [(); 64 * eta1 * 8]:,
    [(); 64 * eta2]:,
    [(); 64 * eta2 * 8]:,
  {
    let (c1, c2) = c.split_at(384 * K);
    let c1 = byte_decode_polyvec::<Monomial, MLKEM_N, K, du>(c1, Monomial);
    let u_prime = polyvec_decompress::<MLKEM_N, du, K>(&c1);
    let v_prime = poly_decompress::<MLKEM_N, dv>(&byte_decode::<dv, MLKEM_N>(c2));

    let s_ntt = byte_decode_polyvec::<Ntt, MLKEM_N, K, 12>(&decryption_key.0, Ntt);
    let w = v_prime - s_ntt.dot_product(&u_prime.ntt()).ntt_inv();
    let m = byte_encode::<1, MLKEM_N>(&poly_compress::<MLKEM_N, 1>(&w).coefficients);
    m.try_into().unwrap()
  }
}

pub struct MlKemEncapsKey<const K: usize>([u8; 384 * K + 32])
where [(); 384 * K + 32]:;
pub struct MlKemDecapsKey<const K: usize>
where [(); 384 * K + 32]: {
  dk_pke: KPkeDecryptionKey<K>,
  ek_pke: KPkeEncryptionKey<K>,
  h:      [u8; 32],
  z:      [u8; 32],
}

pub struct MlKem<const K: usize> {
  kpke: KPke<K>,
}

impl<const K: usize> MlKem<K> {
  fn keygen_internal<const eta1: usize>(
    &self,
    d: [u8; 32],
    z: [u8; 32],
  ) -> (MlKemEncapsKey<K>, MlKemDecapsKey<K>)
  where
    [(); 384 * K + 32]:,
    [(); 768 * K + 96]:,
    [(); 64 * eta1 * 8]:,
  {
    let (ek_pke, dk_pke) = self.kpke.pke_keygen::<eta1>(d);
    let ek: [u8; 384 * K + 32] = ek_pke.0.clone();
    let h = h(&ek);

    (MlKemEncapsKey(ek), MlKemDecapsKey { dk_pke, ek_pke, h, z })
  }

  fn encaps_internal<const eta1: usize, const eta2: usize, const du: usize, const dv: usize>(
    &self,
    ek: MlKemEncapsKey<K>,
    m: [u8; 32],
  ) -> ([u8; 32], Vec<u8>)
  where
    [(); 384 * K + 32]:,
    [(); 64 * eta1]:,
    [(); 64 * eta1 * 8]:,
    [(); 64 * eta2]:,
    [(); 64 * eta2 * 8]:,
  {
    let (k, r) = g([m, h(&ek.0)].concat().as_ref());
    let c = self.kpke.kpke_encrypt::<eta1, eta2, du, dv>(KPkeEncryptionKey(ek.0), m, r);
    (k, c)
  }

  fn decaps_internal<const eta1: usize, const eta2: usize, const du: usize, const dv: usize>(
    &self,
    dk: MlKemDecapsKey<K>,
    c: Vec<u8>,
  ) -> [u8; 32]
  where
    [(); 384 * K + 32]:,
    [(); 64 * eta1]:,
    [(); 64 * eta1 * 8]:,
    [(); 64 * eta2]:,
    [(); 64 * eta2 * 8]:,
  {
    let m_prime = self.kpke.kpke_decrypt::<eta1, eta2, du, dv>(dk.dk_pke, c.clone());
    let (mut k_prime, r_prime) = g([m_prime, dk.h].concat().as_ref());

    let mut pseudo_input = dk.z.to_vec();
    pseudo_input.extend(c.clone());
    let k_bar = auxiliary::j(&pseudo_input);
    let c_prime = self.kpke.kpke_encrypt::<eta1, eta2, du, dv>(dk.ek_pke, m_prime, r_prime);
    if c != c_prime {
      k_prime = k_bar;
    }
    k_prime
  }

  pub fn keygen<const eta1: usize>(
    &self,
  ) -> Result<(MlKemEncapsKey<K>, MlKemDecapsKey<K>), String>
  where
    [(); 384 * K + 32]:,
    [(); 768 * K + 96]:,
    [(); 64 * eta1 * 8]:, {
    // TODO: check if rng is good to use
    let mut rng = rand::thread_rng();
    let d: [u8; 32] = rng.gen::<[u8; 32]>();
    let z = rand::thread_rng().gen::<[u8; 32]>();
    if d.is_empty() || z.is_empty() {
      return Err("Error: keygen failed".to_string());
    }
    Ok(self.keygen_internal::<eta1>(d, z))
  }

  pub fn encaps<const eta1: usize, const eta2: usize, const du: usize, const dv: usize>(
    &self,
    ek: MlKemEncapsKey<K>,
    m: [u8; 32],
  ) -> Result<([u8; 32], Vec<u8>), String>
  where
    [(); 384 * K + 32]:,
    [(); 64 * eta1]:,
    [(); 64 * eta1 * 8]:,
    [(); 64 * eta2]:,
    [(); 64 * eta2 * 8]:,
  {
    // TODO: run encaps key check
    if m.is_empty() {
      return Err("Error: encaps failed".to_string());
    }
    Ok(self.encaps_internal::<eta1, eta2, du, dv>(ek, m))
  }

  pub fn decaps<const eta1: usize, const eta2: usize, const du: usize, const dv: usize>(
    &self,
    dk: MlKemDecapsKey<K>,
    c: Vec<u8>,
  ) -> Result<[u8; 32], String>
  where
    [(); 384 * K + 32]:,
    [(); 64 * eta1]:,
    [(); 64 * eta1 * 8]:,
    [(); 64 * eta2]:,
    [(); 64 * eta2 * 8]:,
  {
    if c.len() != 32 * (du * K + dv) {
      return Err("Error: invalid ciphertext".to_string());
    }

    Ok(self.decaps_internal::<eta1, eta2, du, dv>(dk, c))
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
