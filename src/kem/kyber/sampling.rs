use super::{auxiliary::Xof, MlKemField};
use crate::algebra::{field::Field, Finite};

pub fn sample_ntt(rho: &[u8], j: u8, i: u8) -> [MlKemField; 256] {
  assert!(rho.len() == 32);
  let mut input = [0u8; 34];
  input[..32].copy_from_slice(rho);
  input[32] = j;
  input[33] = i;

  let mut ntt = [MlKemField::ZERO; 256];

  let mut xof = Xof::init().absorb(&input);
  let mut j = 0;
  while j < 256 {
    let mut buf = [0u8; 3];
    Xof::squeeze(&mut xof, &mut buf);

    let d_1 = buf[0] as usize + ((buf[1] as usize & 0xf) << 8);
    let d_2 = (buf[1] >> 4) as usize + ((buf[2] as usize) << 4);

    if d_1 < MlKemField::ORDER {
      ntt[j] = MlKemField::new(d_1);
      j += 1;
    }
    if d_2 < MlKemField::ORDER && j < 256 {
      ntt[j] = MlKemField::new(d_2);
      j += 1;
    }
  }
  ntt
}

pub fn sample_poly_cbd<const ETA: usize>(seed: [u8; 64 * ETA]) -> [MlKemField; 256]
where [(); 64 * ETA * 8]: {
  let mut bit_encode = [0u8; 64 * ETA * 8];
  for i in 0..64 * ETA {
    for j in 0..8 {
      bit_encode[i * 8 + j] = (seed[i] >> j) & 1;
    }
  }

  let mut res = [MlKemField::ZERO; 256];
  for i in 0..256 {
    let x = (0..ETA).fold(0, |acc, j| acc + bit_encode[2 * i * ETA + j]);
    let y = (0..ETA).fold(0, |acc, j| acc + bit_encode[(2 * i + 1) * ETA + j]);
    res[i] = MlKemField::new((x - y) as usize);
  }

  res
}
