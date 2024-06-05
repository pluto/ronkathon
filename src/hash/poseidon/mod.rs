//! Contains implementation of Poseidon Hash function.
#[doc = include_str!("./README.md")]
#[cfg(test)]
mod tests;

use super::Sponge;
use crate::field::FiniteField;

/// Poseidon config used to instantiate hash function
pub struct PoseidonConfig<F: FiniteField> {
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

/// Sponge state that describes current sponge progress.
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
/// * current new elements absorbed into hash state based on the sponge `rate`.
pub struct SpongeConfig {
  rate:          usize,
  capacity:      usize,
  sponge_state:  SpongeState,
  absorb_index:  usize,
  squeeze_index: usize,
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
      parameters: SpongeConfig {
        rate,
        capacity: width - rate,
        sponge_state: SpongeState::Init,
        absorb_index: 0,
        squeeze_index: 0,
      },
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

  /// perform sponge absorption of arbitrary length finite field elements. permutes the state after
  /// each `rate` length chunk has been fully absorbed.
  ///
  /// ## Example
  /// ```ignore
  /// # use rand::rng;
  /// use ronathon::field::prime::PlutoBaseField;
  ///
  /// // create any state
  /// let size = rng.gen::<u32>();
  /// let input = std::iter::repeat(PlutoBaseField::ONE).take(size).collect();
  ///
  /// // load round constants
  /// let (rc, mds) = load_constants::<PlutoBaseField>();
  ///
  /// let mut pluto_poseidon_sponge = PoseidonSponge::new(WIDTH, ALPHA, NUM_P, NUM_F, rate, rc, mds)
  ///
  /// let absorb_res = pluto_poseidon_sponge.absorb(&input);
  /// assert!(absorb_res.is_ok());
  /// ```
  fn absorb(&mut self, elements: &[F]) -> Result<(), &str> {
    // if sponge is in squeezing state, abort
    if self.parameters.sponge_state == SpongeState::Squeezing {
      return Err("sponge is in squeezing mode");
    }

    // update sponge state as absorbing
    self.parameters.sponge_state = SpongeState::Absorbing;

    let mut remaining_elements = elements;

    // new elements not enough for proceesing in chunks
    if self.parameters.absorb_index + remaining_elements.len() <= self.parameters.rate {
      // if new elements doesn't complete current partially filled chunk
      for (i, element) in remaining_elements.iter().enumerate() {
        self.poseidon.state[self.parameters.capacity + self.parameters.absorb_index + i] +=
          *element;
      }
      self.parameters.absorb_index += remaining_elements.len();

      return Ok(());
    } else if self.parameters.absorb_index != 0 {
      // and not enough new elements for chunks, fill current chunk completely and permute
      for (i, element) in remaining_elements
        .iter()
        .take(self.parameters.rate - self.parameters.absorb_index)
        .enumerate()
      {
        self.poseidon.state[self.parameters.capacity + self.parameters.absorb_index + i] +=
          *element;
      }
      remaining_elements =
        &remaining_elements[self.parameters.rate - self.parameters.absorb_index..];
      self.permute();
    }

    let elem_iter = remaining_elements.chunks_exact(self.parameters.rate);
    let remain_elem = elem_iter.remainder().to_vec();

    // process elements in chunks of sponge rate and permute
    for chunk in elem_iter {
      self
        .poseidon
        .state
        .iter_mut()
        .skip(self.parameters.capacity + self.parameters.absorb_index)
        .zip(chunk)
        .for_each(|(a, b)| *a += *b);
      self.permute();
    }

    // take remaining elements and update absorb index
    if !remain_elem.is_empty() {
      for (i, element) in remain_elem.iter().enumerate() {
        self.poseidon.state[self.parameters.capacity + i] += *element;
      }
      self.parameters.absorb_index = remain_elem.len();
    }

    Ok(())
  }

  /// squeezes arbitrary element output
  ///
  /// ## Example
  /// ```ignore
  /// # use rand::rng;
  /// use ronathon::field::prime::PlutoBaseField;
  ///
  /// // create arbitrary length state
  /// let size = rng.gen::<u32>();
  /// let input = std::iter::repeat(PlutoBaseField::ONE).take(size).collect();
  ///
  /// let (rc, mds) = load_constants::<PlutoBaseField>();
  ///
  /// let mut pluto_poseidon_sponge = PoseidonSponge::new(WIDTH, ALPHA, NUM_P, NUM_F, rate, rc, mds)
  ///
  /// // peform absorption any number of times
  /// let _ = pluto_poseidon_sponge.absorb(&input);
  /// let absorb_res = pluto_poseidon_sponge.absorb(&input);
  /// assert!(absorb_res.is_ok());
  ///
  /// // squeeze arbitrary elements output
  /// let pluto_result = pluto_poseidon_sponge.squeeze(squeeze_size);
  /// assert!(pluto_result.is_ok());
  /// ```
  fn squeeze(&mut self, n: usize) -> Result<Vec<F>, &str> {
    if self.parameters.sponge_state == SpongeState::Init {
      return Err("sponge has not absorbed anything");
    } else if self.parameters.sponge_state == SpongeState::Absorbing {
      // if any elements left from previous absorption, perform permutation one last time
      if self.parameters.absorb_index != 0 {
        self.permute();
      }
    }

    // update sponge state to squeezing
    self.parameters.sponge_state = SpongeState::Squeezing;

    let mut result = vec![F::ZERO; n];

    let mut elem_taken = 0;
    loop {
      let elem_left = n - elem_taken;
      if self.parameters.squeeze_index + elem_left <= self.parameters.rate {
        let start_index = self.parameters.capacity + self.parameters.squeeze_index;
        result[elem_taken..]
          .clone_from_slice(&self.poseidon.state[start_index..start_index + elem_left]);

        self.parameters.squeeze_index += elem_left;
        return Ok(result);
      }

      let elements_size =
        std::cmp::min(elem_left, self.parameters.rate - self.parameters.squeeze_index);

      let start_index = self.parameters.capacity + self.parameters.squeeze_index;
      result[elem_taken..elem_taken + elements_size]
        .clone_from_slice(&self.poseidon.state[start_index..start_index + elements_size]);
      self.parameters.squeeze_index += elements_size;

      if self.parameters.squeeze_index == self.parameters.rate {
        self.permute();
        self.parameters.squeeze_index = 0;
      }

      elem_taken += elements_size;
    }
  }
}
