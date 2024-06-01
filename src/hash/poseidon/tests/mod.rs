use super::*;
use crate::field::prime::PlutoBaseField;

mod constants;
use constants::{constants, ALPHA, NUM_F, NUM_P, WIDTH};
use itertools::Itertools;
use rand::{thread_rng, Rng};

fn load_constants<F: FiniteField>() -> (Vec<F>, Vec<Vec<F>>) {
  let (rc, mds) = constants();

  let rc = rc.into_iter().map(|val| F::from(val)).collect_vec();
  let mds =
    mds.into_iter().map(|row| row.into_iter().map(|val| F::from(val)).collect_vec()).collect_vec();

  (rc, mds)
}

fn random_constants<F: FiniteField>(width: usize, num_rounds: usize) -> (Vec<F>, Vec<Vec<F>>)
where rand::distributions::Standard: rand::distributions::Distribution<F> {
  let mut rng = thread_rng();
  let rc: Vec<F> = (0..num_rounds * width).map(|_| rng.gen::<F>()).collect_vec();

  let mut mds: Vec<Vec<F>> = vec![vec![F::ZERO; width]; width];
  for row in mds.iter_mut() {
    *row = (0..width).map(|_| rng.gen::<F>()).collect_vec();
  }
  (rc, mds)
}

#[test]
fn it_works() {
  let (rc, mds) = load_constants::<PlutoBaseField>();
  //   let (rc, mds) = random_constants(WIDTH, NUM_F + NUM_P);
  let mut poseidon = Poseidon::<PlutoBaseField>::new(WIDTH, ALPHA, NUM_P, NUM_F, rc, mds);

  let state = std::iter::repeat(PlutoBaseField::ZERO).take(WIDTH).collect_vec();
  let res = poseidon.hash(state);

  println!("{:?}", res);
}
