//! defines sponge trait for Poseidon hash function. Currently implements only simplex sponge which
//! allows arbitrary length absorption and squeeze.
//!
//! defines Sponge state as structs:
//! - [`Init`]: sponge is initialised with zero state
//! - [`Absorbing`]: sponge is in absorbing state and can absorb arbitrary length of field elements
//! - [`Squeezing`]: sponge can squeeze arbitrary elements
//!
//! ## Example
//! ```ignore
//! # use rand::rng;
//! use ronathon::field::prime::PlutoBaseField;
//! use ronkathon::hashes::poseidon::{PoseidonSponge, Init, Absorbing, Squeezing};
//!
//! // create arbitrary length state
//! let size = rng.gen::<u32>();
//! let input = std::iter::repeat(PlutoBaseField::ONE).take(size).collect();
//!
//! let (rc, mds) = load_constants::<PlutoBaseField>();
//!
//! let mut pluto_poseidon_sponge: PoseidonSponge<PlutoBaseField, Init> = PoseidonSponge::new(WIDTH, ALPHA, NUM_P, NUM_F, rate, rc,mds)
//!
//! // perform absorption any number of times
//! let mut pluto_poseidon_sponge: PoseidonSponge<PlutoBaseField, Absorbing> = pluto_poseidon_sponge.start_absorbing();
//!  let _ = pluto_poseidon_sponge.absorb(&input);
//! let absorb_res = pluto_poseidon_sponge.absorb(&input);
//! assert!(absorb_res.is_ok());
//!
//! // squeeze arbitrary elements output
//! let mut pluto_poseidon_sponge: PoseidonSponge<PlutoBaseField, Squeezing> = pluto_poseidon_sponge.start_squeezing();
//! let pluto_result = pluto_poseidon_sponge.squeeze(squeeze_size);
//! assert!(pluto_result.is_ok());
//! ```
use std::marker::PhantomData;

use super::Poseidon;
use crate::{hashes::Sponge, Field};

/// initialised sponge state
pub struct Init;
/// absorbing sponge state
pub struct Absorbing;
/// squeezing sponge state
pub struct Squeezing;

/// Sponge config containing sponge rate, and state
/// * `rate` describes number of elements absorbed by sponge before any permutation round
/// * `sponge_state` describes current sponge state. Initialised in [`Init`] state and, if sponge is
///   squeezing, then it can't absorb new elements.
/// * current new elements absorbed into hash state based on the sponge `rate`.
#[derive(Debug, Clone)]
pub struct SpongeConfig<S> {
  rate:          usize,
  capacity:      usize,
  absorb_index:  usize,
  squeeze_index: usize,
  sponge_state:  PhantomData<S>,
}

/// Poseidon sponge object with poseidon object. Contains:
/// * `poseidon` - [`Poseidon`] struct with hash state, and config
/// * `parameters` - [`SpongeConfig`] with sponge related parameters like `rate` and `absorb_index`
#[derive(Debug, Clone)]
pub struct PoseidonSponge<F: Field, S> {
  poseidon:   Poseidon<F>,
  parameters: SpongeConfig<S>,
}

impl<F: Field, S> PoseidonSponge<F, S> {
  /// create new poseidon sponge object with [`Poseidon`] hash object and [`SpongeConfig`]
  pub fn new(
    width: usize,
    alpha: usize,
    num_p: usize,
    num_f: usize,
    rate: usize,
    rc: Vec<F>,
    mds: Vec<Vec<F>>,
  ) -> PoseidonSponge<F, Init> {
    let poseidon = Poseidon::new(width, alpha, num_p, num_f, rc, mds);

    PoseidonSponge {
      poseidon,
      parameters: SpongeConfig {
        rate,
        capacity: width - rate,
        sponge_state: PhantomData,
        absorb_index: 0,
        squeeze_index: 0,
      },
    }
  }

  /// perform hash operation of sponge state and reset absorb index to 0 for new elements to be
  /// absorbed.
  fn permute(&mut self) {
    let _ = self.poseidon.hash(self.poseidon.state.clone());
    self.parameters.absorb_index = 0;
  }
}

impl<F: Field> PoseidonSponge<F, Init> {
  /// start absorption stage of a sponge
  pub fn start_absorbing(self) -> PoseidonSponge<F, Absorbing> {
    PoseidonSponge {
      poseidon:   self.poseidon,
      parameters: SpongeConfig {
        rate:          self.parameters.rate,
        capacity:      self.parameters.capacity,
        absorb_index:  self.parameters.absorb_index,
        squeeze_index: self.parameters.squeeze_index,
        sponge_state:  PhantomData,
      },
    }
  }
}

impl<F: Field> PoseidonSponge<F, Absorbing> {
  /// perform sponge absorption of arbitrary length finite field elements. permutes the state after
  /// each `rate` length chunk has been fully absorbed.
  ///
  /// ## Example
  /// ```ignore
  /// # use rand::rng;
  /// use ronathon::field::prime::PlutoBaseField;
  /// use ronkathon::hashes::poseidon::{PoseidonSponge, Init, Absorbing};
  ///
  /// // create any state
  /// let size = rng.gen::<u32>();
  /// let input = std::iter::repeat(PlutoBaseField::ONE).take(size).collect();
  ///
  /// // load round constants
  /// let (rc, mds) = load_constants::<PlutoBaseField>();
  ///
  /// let mut pluto_poseidon_sponge: PoseidonSponge<PlutoBaseField, Init> = PoseidonSponge::new(WIDTH, ALPHA, NUM_P, NUM_F, rate, rc,mds)
  ///
  /// let mut pluto_poseidon_sponge: PoseidonSponge<PlutoBaseField, Absorbing> = pluto_poseidon_sponge.start_absorbing();
  ///
  /// let absorb_res = pluto_poseidon_sponge.absorb(&input);
  /// assert!(absorb_res.is_ok());
  /// ```
  pub fn absorb(&mut self, elements: &[F]) -> Result<&mut Self, &str> {
    let mut remaining_elements = elements;

    // new elements not enough for processing in chunks
    if self.parameters.absorb_index + remaining_elements.len() <= self.parameters.rate {
      // if new elements doesn't complete current partially filled chunk
      for (i, element) in remaining_elements.iter().enumerate() {
        self.poseidon.state[self.parameters.capacity + self.parameters.absorb_index + i] +=
          *element;
      }
      self.parameters.absorb_index += remaining_elements.len();

      return Ok(self);
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

    Ok(self)
  }

  /// transition to squeezing state of a sponge, permute the state, if any elements left from
  /// absorption
  pub fn start_squeezing(&mut self) -> PoseidonSponge<F, Squeezing> {
    if self.parameters.absorb_index != 0 {
      self.permute();
    }

    PoseidonSponge {
      poseidon:   self.poseidon.clone(),
      parameters: SpongeConfig {
        rate:          self.parameters.rate,
        capacity:      self.parameters.capacity,
        absorb_index:  self.parameters.absorb_index,
        squeeze_index: self.parameters.squeeze_index,
        sponge_state:  PhantomData,
      },
    }
  }
}

impl<F: Field> PoseidonSponge<F, Squeezing> {
  /// squeezes arbitrary element output
  ///
  /// ## Example
  /// ```ignore
  /// # use rand::rng;
  /// use ronathon::field::prime::PlutoBaseField;
  /// use ronkathon::hashes::poseidon::{PoseidonSponge, Init, Absorbing, Squeezing};
  ///
  /// // create arbitrary length state
  /// let size = rng.gen::<u32>();
  /// let input = std::iter::repeat(PlutoBaseField::ONE).take(size).collect();
  ///
  /// let (rc, mds) = load_constants::<PlutoBaseField>();
  ///
  /// let mut pluto_poseidon_sponge: PoseidonSponge<PlutoBaseField, Init> = PoseidonSponge::new(WIDTH, ALPHA, NUM_P, NUM_F, rate, rc,mds)
  ///
  /// // perform absorption any number of times
  /// let mut pluto_poseidon_sponge: PoseidonSponge<PlutoBaseField, Absorbing> = pluto_poseidon_sponge.start_absorbing();
  ///  let _ = pluto_poseidon_sponge.absorb(&input);
  /// let absorb_res = pluto_poseidon_sponge.absorb(&input);
  /// assert!(absorb_res.is_ok());
  ///
  /// // squeeze arbitrary elements output
  /// let mut pluto_poseidon_sponge: PoseidonSponge<PlutoBaseField, Squeezing> = pluto_poseidon_sponge.start_squeezing();
  /// let pluto_result = pluto_poseidon_sponge.squeeze(squeeze_size);
  /// assert!(pluto_result.is_ok());
  /// ```
  pub fn squeeze(&mut self, n: usize) -> Result<Vec<F>, &str> {
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

impl<F: Field> Sponge<F> for PoseidonSponge<F, Absorbing> {
  fn permute(&mut self) { self.permute(); }

  fn absorb(&mut self, elements: &[F]) -> Result<(), &str> {
    self.absorb(elements)?;
    Ok(())
  }

  fn squeeze(&mut self, _: usize) -> Result<Vec<F>, &str> { Err("sponge is in squeeze state") }
}

impl<F: Field> Sponge<F> for PoseidonSponge<F, Squeezing> {
  fn permute(&mut self) { self.permute(); }

  fn absorb(&mut self, _: &[F]) -> Result<(), &str> { Err("sponge is in squeezing state") }

  fn squeeze(&mut self, n: usize) -> Result<Vec<F>, &str> { self.squeeze(n) }
}
