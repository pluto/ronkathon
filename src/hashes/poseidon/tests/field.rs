use ark_ff::{Fp64, MontBackend, MontConfig};

use super::constants::constants;

#[derive(MontConfig)]
#[modulus = "101"]
#[generator = "2"]
pub struct FrBackend;
type FrConfig = MontBackend<FrBackend, 1>;
pub type Fr = Fp64<FrConfig>;

pub fn ark_constants(width: usize) -> (Vec<Vec<Fr>>, Vec<Vec<Fr>>) {
  let (rc, mds) = constants();
  let mds =
    mds.into_iter().map(|row| row.into_iter().map(|val| Fr::from(val as u32)).collect()).collect();

  let mut rc_2d = Vec::new();
  for chunk in rc.chunks(width) {
    rc_2d.push(chunk.iter().map(|val| Fr::from(*val as u32)).collect());
  }
  (rc_2d, mds)
}
