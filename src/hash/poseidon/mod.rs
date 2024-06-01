//! contains implementation of poseidon hash function
#[cfg(test)] mod tests;

use crate::field::FiniteField;

/// Poseidon config used to instantiate hash function
pub struct PoseidonConfig<F: FiniteField> {
  /// alpha used during sbox layer to raise the state by
  pub alpha:           usize,
  /// width of the hash function
  pub width:           usize,
  /// number of partial rounds
  pub num_p:           usize,
  /// number of full rounds
  pub num_f:           usize,
  /// minimum distance separable matrix used to mix the layer
  pub mds_matrix:      Vec<Vec<F>>,
  /// round constants added to state at each round
  pub round_constants: Vec<F>,
}

/// Poseidon hash function struct with state and config
pub struct Poseidon<F: FiniteField> {
  state:  Vec<F>,
  config: PoseidonConfig<F>,
}

impl<F: FiniteField> PoseidonConfig<F> {
  fn new(
    width: usize,
    alpha: usize,
    num_p: usize,
    num_f: usize,
    rc: Vec<F>,
    mds: Vec<Vec<F>>,
  ) -> Self {
    assert!(width > 1, "hash width should be greater than 1");
    assert_eq!(mds.len(), width, "mds matrix should be as long as width");
    assert_eq!(
      rc.len(),
      (num_p + num_f) * width,
      "round constants should be equal to number of full and partial rounds",
    );

    PoseidonConfig { width, alpha, num_f, num_p, mds_matrix: mds, round_constants: rc }
  }
}

impl<F: FiniteField> Poseidon<F> {
  /// instantiate hash function with required config
  pub fn new(
    width: usize,
    alpha: usize,
    num_p: usize,
    num_f: usize,
    rc: Vec<F>,
    mds: Vec<Vec<F>>,
  ) -> Self {
    Poseidon {
      state:  vec![],
      config: PoseidonConfig::<F>::new(width, alpha, num_p, num_f, rc, mds),
    }
  }

  fn sbox_full(&mut self) {
    for state in self.state.iter_mut() {
      *state = state.pow(self.config.alpha);
    }
  }

  fn sbox_partial(&mut self) { self.state[0] = self.state[0].pow(self.config.alpha); }

  fn sbox(&mut self, round_i: usize) {
    if round_i < self.config.num_p / 2 || round_i > self.config.num_p / 2 + self.config.num_f {
      self.sbox_full()
    } else {
      self.sbox_partial()
    }
  }

  fn product_mds(&mut self) {
    let mut new_state: Vec<F> = Vec::with_capacity(self.config.width + 1);
    for i in 0..self.config.width {
      let mut new_state_i = F::ZERO;
      for j in 0..self.config.width {
        new_state_i += self.state[j] * self.config.mds_matrix[i][j];
      }
      new_state.push(new_state_i);
    }
    self.state = new_state
  }

  fn add_round_constants(&mut self, ith: usize) {
    for (i, state) in self.state.iter_mut().enumerate() {
      // println!(
      //     "ark: {:?}, state: {:?}",
      //     self.params.round_constants.len(),
      //     self.state.len()
      // );
      *state += self.config.round_constants[ith * self.config.width + i];
    }
  }

  /// perform the hashing on elements of state. state is padded by zero values, if not equal to
  /// width of the hash function
  pub fn hash(&mut self, mut state: Vec<F>) -> Result<F, String> {
    state.extend(std::iter::repeat(F::ZERO).take(self.config.width - state.len()));
    self.state = state;

    let num_rounds = self.config.num_f + self.config.num_p;
    for i in 0..num_rounds {
      // println!("start round_i: {}, state: {:?}", i, self.state.len());
      self.add_round_constants(i);
      // println!("ark round_i: {}, state: {:?}", i, self.state.len());
      self.sbox(i);
      // println!("sbox round_i: {}, state: {:?}", i, self.state.len());
      self.product_mds();
      // println!("end round_i: {}, state: {:?}", i, self.state.len());
    }

    Ok(self.state[1])
  }
}
