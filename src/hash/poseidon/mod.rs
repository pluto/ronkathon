//! Contains implementation of Poseidon Hash function
#[doc = include_str!("./README.md")]
#[cfg(test)]
mod tests;

use super::Sponge;
use crate::field::FiniteField;

/// Poseidon config used to instantiate hash function
pub struct PoseidonConfig<F: FiniteField> {
  /// alpha used during sbox layer to raise the state by. Used during non-linear layer of the
  /// permutation to mix the elements.
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
/// state contains current hash state of [`PoseidonConfig::width`] length and [`PoseidonConfig`]
/// contains config for rounds in the hash function.
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
      state:  vec![F::ZERO; width],
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
      *state += self.config.round_constants[ith * self.config.width + i];
    }
  }

  /// perform the hashing on elements of state. state is padded by zero values, if not equal to
  /// width of the hash function
  pub fn hash(&mut self, mut state: Vec<F>) -> F {
    state.extend(std::iter::repeat(F::ZERO).take(self.config.width - state.len()));
    self.state = state;

    let num_rounds = self.config.num_f + self.config.num_p;
    for i in 0..num_rounds {
      self.add_round_constants(i);
      self.sbox(i);
      self.product_mds();
    }

    self.state[1]
  }
}

/// Sponge state that describes current sponge progress
#[derive(Clone, Copy, PartialEq)]
pub enum SpongeState {
  /// Sponge is initialised with state marked as zero
  Init,
  /// Sponge is absorbing elements
  Absorbing,
  /// Sponge is squeezing elements.
  Squeezing,
}

/// Sponge config containing sponge rate, and state
/// * `rate` describes number of elements absorbed by sponge before any permutation round
/// * `sponge_state` describes current [`SpongeState`]. Initialised in [`SpongeState::Init`] state
///   and, if sponge is squeezing, then it can't absorb new elements.
/// absorb again.
/// * current new elements absorbed into hash state based on the sponge `rate`.
pub struct SpongeConfig {
  rate:         usize,
  sponge_state: SpongeState,
  absorb_index: usize,
}

/// Poseidon sponge object with poseidon object. Contains:
/// * `poseidon` - [`Poseidon`] struct with hash state, and config
/// * `parameters` - [`SpongeConfig`] with sponge related parameters like `rate`, `sponge_state`,
///   and `absorb_index`
pub struct PoseidonSponge<F: FiniteField> {
  poseidon:   Poseidon<F>,
  parameters: SpongeConfig,
}

impl<F: FiniteField> PoseidonSponge<F> {
  /// create new poseidon sponge object with [`Poseidon`] hash object and [`SpongeConfig`]
  pub fn new(
    width: usize,
    alpha: usize,
    num_p: usize,
    num_f: usize,
    rate: usize,
    rc: Vec<F>,
    mds: Vec<Vec<F>>,
  ) -> Self {
    let poseidon = Poseidon::new(width, alpha, num_p, num_f, rc, mds);
    PoseidonSponge {
      poseidon,
      parameters: SpongeConfig { rate, sponge_state: SpongeState::Init, absorb_index: 0 },
    }
  }
}

impl<F: FiniteField> Sponge<F> for PoseidonSponge<F> {
  /// perform hash operation of sponge state and reset absorb index to 0 for new elements to be
  /// absorbed.
  fn permute(&mut self) {
    let _ = self.poseidon.hash(self.poseidon.state.clone());
    self.parameters.absorb_index = 0;
  }

  fn absorb(&mut self, elements: &[F]) -> Result<(), &str> {
    // if sponge is in squeezing state, abort
    if self.parameters.sponge_state == SpongeState::Squeezing {
      return Err("sponge is in squeezing mode");
    }

    // update sponge state as absorbing
    self.parameters.sponge_state = SpongeState::Absorbing;

    // new elements not enough for proceesing in chunks
    if self.parameters.absorb_index + elements.len() < self.parameters.rate {
      // if new elements length < absorb index + rate
      for (i, element) in elements.iter().enumerate() {
        self.poseidon.state[self.parameters.absorb_index + i] += *element;
      }
      self.parameters.absorb_index += elements.len();

      return Ok(());
    } else if elements.len() < self.parameters.rate {
      // and not enough new elements for chunks
      for (i, element) in
        elements.iter().take(self.parameters.rate - self.parameters.absorb_index).enumerate()
      {
        self.poseidon.state[self.parameters.absorb_index + i] += *element;
      }
      self.permute();
    }

    let elem_iter = elements.chunks_exact(self.parameters.rate);

    // take remaining elements and update absorb index
    self.poseidon.state = elem_iter.remainder().to_vec();
    self.parameters.absorb_index = self.poseidon.state.len();

    // process elements in chunks of sponge rate and permute
    for chunk in elem_iter {
      self.poseidon.state.iter_mut().zip(chunk).for_each(|(a, b)| *a += *b);
      self.permute();
    }

    Ok(())
  }

  fn squeeze(&mut self, n: usize) -> Result<Vec<F>, &str> {
    if self.parameters.sponge_state == SpongeState::Init {
      return Err("sponge has not absorbed anything");
    }

    // update sponge state to squeezing
    self.parameters.sponge_state = SpongeState::Squeezing;

    // if any elements left from previous absorption, perform permutation one last time
    if self.parameters.absorb_index != 0 {
      self.permute();
    }

    let result = (0..n).map(|_| self.poseidon.hash(self.poseidon.state.clone())).collect();
    Ok(result)
  }
}
