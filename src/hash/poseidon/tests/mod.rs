use super::*;
use crate::field::prime::PlutoBaseField;

mod constants;
use constants::{constants, ALPHA, NUM_F, NUM_P, WIDTH};
use rand::{thread_rng, Rng};
mod small_field;

extern crate ff;

fn load_constants<F: FiniteField>() -> (Vec<F>, Vec<Vec<F>>) {
  let (rc, mds) = constants();

  let rc = rc.into_iter().map(|val| F::from(val)).collect();
  let mds = mds.into_iter().map(|row| row.into_iter().map(|val| F::from(val)).collect()).collect();

  (rc, mds)
}

fn random_constants<F: FiniteField>(width: usize, num_rounds: usize) -> (Vec<F>, Vec<Vec<F>>)
where rand::distributions::Standard: rand::distributions::Distribution<F> {
  let mut rng = thread_rng();
  let rc: Vec<F> = (0..num_rounds * width).map(|_| rng.gen::<F>()).collect();

  let mut mds: Vec<Vec<F>> = vec![vec![F::ZERO; width]; width];
  for row in mds.iter_mut() {
    *row = (0..width).map(|_| rng.gen::<F>()).collect();
  }
  (rc, mds)
}

#[test]
fn it_works() {
  let (rc, mds) = load_constants::<PlutoBaseField>();
  //   let (rc, mds) = random_constants(WIDTH, NUM_F + NUM_P);
  let mut poseidon = Poseidon::<PlutoBaseField>::new(WIDTH, ALPHA, NUM_P, NUM_F, rc, mds);

  let state = std::iter::repeat(PlutoBaseField::ZERO).take(WIDTH).collect();
  let res = poseidon.hash(state);

  println!("{:?}", res);
}

#[test]
fn poseidon_sponge() {
  let (rc, mds) = load_constants::<PlutoBaseField>();

  let size = 24;
  let elements = std::iter::repeat(PlutoBaseField::ONE).take(size).collect::<Vec<PlutoBaseField>>();
  let mut poseidon_sponge = PoseidonSponge::new(WIDTH, ALPHA, NUM_P, NUM_F, 6, rc, mds);
  let absorb_res = poseidon_sponge.absorb(&elements);
  assert!(absorb_res.is_ok());

  let hash_result = poseidon_sponge.squeeze(4);
  assert!(hash_result.is_ok());

  println!("{:?}", hash_result.unwrap());
}

#[test]
fn ark_poseidon() {}
