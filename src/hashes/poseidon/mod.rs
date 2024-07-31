//! Contains implementation of Poseidon Hash function.
#![cfg_attr(not(doctest), doc = include_str!("./README.md"))]
#[cfg(test)] mod tests;

pub mod sponge;

pub use sponge::*;

use crate::Field;

/// Poseidon config used to instantiate hash function
#[derive(Debug, Clone)]
pub struct PoseidonConfig<F: Field> {
  /// alpha used during sbox layer calculate `x^{alpha}`
  alpha:           usize,
  /// width of the hash function that decides how many elements of finite field are stored in the
  /// state of hash function at each step
  width:           usize,
  /// number of partial rounds
  num_p:           usize,
  /// number of full rounds
  num_f:           usize,
  /// minimum distance separable matrix used to mix the state at linear layer
  mds_matrix:      Vec<Vec<F>>,
  /// round constants added to state at the beginning of each round
  round_constants: Vec<F>,
}

/// Poseidon hash function struct with state and config
/// state contains current hash state of `width` length and [`PoseidonConfig`]
/// contains config for rounds in the hash function.
#[derive(Debug, Clone)]
pub struct Poseidon<F: Field> {
  state:  Vec<F>,
  config: PoseidonConfig<F>,
}

impl<F: Field> PoseidonConfig<F> {
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

impl<F: Field> Poseidon<F> {
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
      state:  vec![F::ZERO; width],
      config: PoseidonConfig::<F>::new(width, alpha, num_p, num_f, rc, mds),
    }
  }

  /// applies sbox in the full round. Raises the state by [`PoseidonConfig::alpha`].
  fn sbox_full(&mut self) {
    for state in self.state.iter_mut() {
      *state = state.pow(self.config.alpha);
    }
  }

  /// applies sbox in partial round. Raises first element by [`PoseidonConfig::alpha`]
  fn sbox_partial(&mut self) { self.state[0] = self.state[0].pow(self.config.alpha); }

  /// applies non-linear layer of the round in the form of s-boxes. Partial rounds are sandwiched
  /// between half full rounds.
  fn apply_non_linear_layer(&mut self, round_i: usize) {
    if round_i < self.config.num_f / 2 || round_i >= self.config.num_p + self.config.num_f / 2 {
      self.sbox_full()
    } else {
      self.sbox_partial()
    }
  }

  /// applies linear layer of the round by multiplying the state with MDS matrix to mix the elements
  fn apply_linear_layer(&mut self) {
    let mut new_state: Vec<F> = Vec::new();
    for i in 0..self.config.width {
      let mut new_state_i = F::ZERO;
      for (j, state_elem) in self.state.iter().enumerate() {
        new_state_i += *state_elem * self.config.mds_matrix[i][j];
      }
      new_state.push(new_state_i);
    }
    self.state = new_state
  }

  /// adds round constants to the state to break the symmetricity in the state
  fn add_round_constants(&mut self, ith: usize) {
    for (i, state) in self.state.iter_mut().enumerate() {
      *state += self.config.round_constants[ith * self.config.width + i];
    }
  }

  /// perform the hashing on elements of state. state is padded by zero values, if not equal to
  /// width of the hash function.
  /// ## Example
  /// ```ignore
  /// use ronkathon::field::prime::PlutoBaseField;
  ///
  /// // Poseidon parameters
  /// const WIDTH: usize = 10;
  /// const ALPHA: usize = 5;
  /// const NUM_P: usize = 16;
  /// const NUM_F: usize = 8;
  /// // load round constants and mds matrix
  /// let (rc, mds) = load_constants::<PlutoBaseField>();
  ///
  /// // create a poseidon hash object with empty state
  /// let mut poseidon = Poseidon::<PlutoBaseField>::new(WIDTH, ALPHA, NUM_P, NUM_F, rc, mds);
  ///
  /// // create any input
  /// let input = std::iter::repeat(PlutoBaseField::ZERO).take(WIDTH).collect();
  ///
  /// let res = poseidon.hash(input);
  /// ```
  pub fn hash(&mut self, mut state: Vec<F>) -> F {
    state.extend(std::iter::repeat(F::ZERO).take(self.config.width - state.len()));
    self.state = state;

    let num_rounds = self.config.num_f + self.config.num_p;
    for i in 0..num_rounds {
      self.add_round_constants(i);
      self.apply_non_linear_layer(i);
      self.apply_linear_layer();
    }

    self.state[1]
  }
}
