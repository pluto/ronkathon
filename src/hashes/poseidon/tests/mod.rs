use super::*;
use crate::PlutoBaseField;
mod constants;
use rstest::{fixture, rstest};

use crate::hashes::{
  poseidon::tests::field::{ark_constants, Fr},
  Sponge,
};
mod field;
use ark_crypto_primitives::sponge::{
  poseidon::{self, PoseidonSponge as ArkPoseidonSponge},
  CryptographicSponge, FieldBasedCryptographicSponge,
};
use constants::{constants, ALPHA, NUM_F, NUM_P, WIDTH};
use rand::{thread_rng, Rng};

fn load_constants<F: Field>() -> (Vec<F>, Vec<Vec<F>>) {
  let (rc, mds) = constants();

  let rc = rc.into_iter().map(|val| F::from(val)).collect();
  let mds = mds.into_iter().map(|row| row.into_iter().map(|val| F::from(val)).collect()).collect();

  (rc, mds)
}

#[allow(dead_code)]
fn random_constants<F: Field>(width: usize, num_rounds: usize) -> (Vec<F>, Vec<Vec<F>>)
where rand::distributions::Standard: rand::distributions::Distribution<F> {
  let mut rng = thread_rng();
  let rc: Vec<F> = (0..num_rounds * width).map(|_| rng.gen::<F>()).collect();

  let mut mds: Vec<Vec<F>> = vec![vec![F::ZERO; width]; width];
  for row in mds.iter_mut() {
    *row = (0..width).map(|_| rng.gen::<F>()).collect();
  }
  (rc, mds)
}
#[allow(unused_braces)]
#[fixture]
fn rate() -> usize { 6 }

fn input(absorb_size: usize) -> (Vec<PlutoBaseField>, Vec<Fr>) {
  let mut rng = thread_rng();
  let mut pluto_input = Vec::new();
  let mut ark_input = Vec::new();

  for _ in 0..absorb_size {
    let elem = rng.gen::<u32>();
    pluto_input.push(PlutoBaseField::from(elem));
    ark_input.push(Fr::from(elem));
  }

  (pluto_input, ark_input)
}

#[fixture]
fn pluto_poseidon() -> Poseidon<PlutoBaseField> {
  let (rc, mds) = load_constants::<PlutoBaseField>();
  Poseidon::new(WIDTH, ALPHA, NUM_P, NUM_F, rc, mds)
}

#[fixture]
fn pluto_poseidon_sponge(rate: usize) -> PoseidonSponge<PlutoBaseField, Init> {
  let (rc, mds) = load_constants::<PlutoBaseField>();
  //   let (rc, mds) = random_constants(WIDTH, NUM_F + NUM_P);
  PoseidonSponge::<PlutoBaseField, Init>::new(WIDTH, ALPHA, NUM_P, NUM_F, rate, rc, mds)
}

#[fixture]
fn ark_poseidon(rate: usize) -> ArkPoseidonSponge<Fr> {
  let (ark, mds_ark) = ark_constants(WIDTH);
  let poseidon_config = poseidon::PoseidonConfig::new(
    NUM_F,
    NUM_P,
    ALPHA as u64,
    mds_ark.clone(),
    ark.clone(),
    rate,
    WIDTH - rate,
  );
  ArkPoseidonSponge::new(&poseidon_config)
}

#[rstest]
fn hash(mut pluto_poseidon: Poseidon<PlutoBaseField>) {
  let state = std::iter::repeat(PlutoBaseField::ZERO).take(WIDTH).collect();
  let res = pluto_poseidon.hash(state);

  assert_eq!(res, PlutoBaseField::new(20));
}

#[test]
#[should_panic]
fn invalid_poseidon_config_width() {
  PoseidonConfig::<PlutoBaseField>::new(1, ALPHA, NUM_P, NUM_F, vec![], vec![]);
}

#[test]
#[should_panic]
fn invalid_poseidon_config_mds() {
  PoseidonConfig::<PlutoBaseField>::new(WIDTH, ALPHA, NUM_P, NUM_F, vec![], vec![]);
}

#[test]
#[should_panic]
fn invalid_poseidon_config_ark() {
  let (_, mds) = load_constants::<PlutoBaseField>();
  PoseidonConfig::<PlutoBaseField>::new(WIDTH, ALPHA, NUM_P, NUM_F, vec![], mds);
}

#[rstest]
#[case(1, 1)]
#[case(2, 2)]
#[case(5, 10)]
#[case(6, 4)]
#[case(14, 10)]
#[case(25, 20)]
fn poseidon_sponge_single_absorb_squeeze(
  pluto_poseidon_sponge: PoseidonSponge<PlutoBaseField, Init>,
  mut ark_poseidon: ArkPoseidonSponge<Fr>,
  #[case] absorb_size: usize,
  #[case] squeeze_size: usize,
) {
  let input = input(absorb_size);

  let mut pluto_poseidon_sponge = pluto_poseidon_sponge.start_absorbing();
  let absorb_res = pluto_poseidon_sponge.absorb(&input.0);
  assert!(absorb_res.is_ok());

  let mut pluto_poseidon_sponge = pluto_poseidon_sponge.start_squeezing();
  let pluto_result = pluto_poseidon_sponge.squeeze(squeeze_size);
  assert!(pluto_result.is_ok());

  let pluto_result = pluto_result.unwrap();

  ark_poseidon.absorb(&input.1);

  let ark_result = ark_poseidon.squeeze_native_field_elements(squeeze_size);

  let ark_result: Vec<String> = ark_result.into_iter().map(|val| val.to_string()).collect();
  let pluto_result: Vec<String> = pluto_result.into_iter().map(|val| val.to_string()).collect();

  assert_eq!(ark_result, pluto_result);
}

#[rstest]
fn abosrb_after_squeeze(pluto_poseidon_sponge: PoseidonSponge<PlutoBaseField, Init>) {
  let size = 5;
  let squeeze_size = 2;

  let elements = std::iter::repeat(PlutoBaseField::ONE + PlutoBaseField::ONE)
    .take(size)
    .collect::<Vec<PlutoBaseField>>();

  let mut pluto_poseidon_sponge = pluto_poseidon_sponge.start_absorbing();

  let _ = pluto_poseidon_sponge.absorb(&elements);

  let mut pluto_poseidon_sponge = pluto_poseidon_sponge.start_squeezing();

  let _ = pluto_poseidon_sponge.squeeze(squeeze_size);

  let res = pluto_poseidon_sponge.absorb(&elements);
  assert!(res.is_err());
}

#[rstest]
#[case(1, 2, 2)]
#[case(3, 4, 4)]
#[case(5, 8, 3)]
#[case(7, 4, 7)]
#[case(15, 5, 9)]
fn poseidon_sponge_multiple_absorb_single_squeeze(
  pluto_poseidon_sponge: PoseidonSponge<PlutoBaseField, Init>,
  mut ark_poseidon: ArkPoseidonSponge<Fr>,
  #[case] absorb_size: usize,
  #[case] absorb_time: usize,
  #[case] squeeze_size: usize,
) {
  let input = input(absorb_size);
  let mut pluto_poseidon_sponge = pluto_poseidon_sponge.start_absorbing();

  for _ in 0..absorb_time {
    let absorb_res = pluto_poseidon_sponge.absorb(&input.0);
    assert!(absorb_res.is_ok());
  }

  let mut pluto_poseidon_sponge = pluto_poseidon_sponge.start_squeezing();

  let pluto_result = pluto_poseidon_sponge.squeeze(squeeze_size);
  assert!(pluto_result.is_ok());

  let pluto_result = pluto_result.unwrap();

  for _ in 0..absorb_time {
    ark_poseidon.absorb(&input.1);
  }

  let ark_result = ark_poseidon.squeeze_native_field_elements(squeeze_size);

  let ark_result: Vec<String> = ark_result.into_iter().map(|val| val.to_string()).collect();
  let pluto_result: Vec<String> = pluto_result.into_iter().map(|val| val.to_string()).collect();

  assert_eq!(ark_result, pluto_result);
}

#[rstest]
#[case(1, 2, 2, 2)]
#[case(3, 4, 4, 4)]
#[case(5, 8, 3, 7)]
#[case(6, 4, 7, 10)]
#[case(17, 14, 12, 17)]
fn poseidon_sponge_multiple_absorb_multiple_squeeze(
  pluto_poseidon_sponge: PoseidonSponge<PlutoBaseField, Init>,
  mut ark_poseidon: ArkPoseidonSponge<Fr>,
  #[case] absorb_size: usize,
  #[case] absorb_time: usize,
  #[case] squeeze_size: usize,
  #[case] squeeze_time: usize,
) {
  let input = input(absorb_size);
  let mut pluto_poseidon_sponge = pluto_poseidon_sponge.start_absorbing();

  for _ in 0..absorb_time {
    let absorb_res = pluto_poseidon_sponge.absorb(&input.0);
    assert!(absorb_res.is_ok());
  }

  for _ in 0..absorb_time {
    ark_poseidon.absorb(&input.1);
  }

  let mut pluto_poseidon_sponge = pluto_poseidon_sponge.start_squeezing();

  for _ in 0..squeeze_time {
    let pluto_result = pluto_poseidon_sponge.squeeze(squeeze_size);
    assert!(pluto_result.is_ok());

    let pluto_result = pluto_result.unwrap();

    let ark_result = ark_poseidon.squeeze_native_field_elements(squeeze_size);

    let ark_result: Vec<String> = ark_result.into_iter().map(|val| val.to_string()).collect();
    let pluto_result: Vec<String> = pluto_result.into_iter().map(|val| val.to_string()).collect();

    assert_eq!(ark_result, pluto_result);
  }
}

#[rstest]
#[case(4, 4, 4)]
#[case(1, 15, 2)]
fn poseidon_sponge_multiple_absorb_vs_one_time_absorb(
  #[from(pluto_poseidon_sponge)] pluto_poseidon_sponge1: PoseidonSponge<PlutoBaseField, Init>,
  #[from(pluto_poseidon_sponge)] pluto_poseidon_sponge2: PoseidonSponge<PlutoBaseField, Init>,
  #[case] absorb_size: usize,
  #[case] absorb_time: usize,
  #[case] squeeze_size: usize,
) {
  let input1 = input(absorb_size);

  let mut pluto_poseidon_sponge1 = pluto_poseidon_sponge1.start_absorbing();

  for _ in 0..absorb_time {
    let absorb_res = pluto_poseidon_sponge1.absorb(&input1.0);
    assert!(absorb_res.is_ok());
  }

  let mut pluto_poseidon_sponge1 = pluto_poseidon_sponge1.start_squeezing();

  let pluto_result = pluto_poseidon_sponge1.squeeze(squeeze_size);
  assert!(pluto_result.is_ok());

  let hash_result1 = pluto_result.unwrap();

  let mut input2 = input1.0.clone();
  for _ in 0..absorb_time - 1 {
    input2.extend_from_within(..absorb_size);
  }

  let mut pluto_poseidon_sponge2 = pluto_poseidon_sponge2.start_absorbing();

  let absorb_res = pluto_poseidon_sponge2.absorb(&input2);
  assert!(absorb_res.is_ok());

  let mut pluto_poseidon_sponge2 = pluto_poseidon_sponge2.start_squeezing();

  let hash_result2 = pluto_poseidon_sponge2.squeeze(squeeze_size);
  assert!(hash_result2.is_ok());
  let hash_result2 = hash_result2.unwrap();

  let hash_result1: Vec<String> = hash_result1.into_iter().map(|val| val.to_string()).collect();
  let hash_result2: Vec<String> = hash_result2.into_iter().map(|val| val.to_string()).collect();

  assert_eq!(hash_result1, hash_result2);
}
