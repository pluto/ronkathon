//! Counter used during various encryption primitives for randomising IV in reduced bandwidth
//! scenarios. Implements a simple increment by one counter.

/// Counter consisting of big-endian integer using byte(8-bit) limbs
#[derive(Debug, Clone, Copy)]
pub struct Counter<const C: usize>(pub [u8; C]);

impl<const C: usize> Counter<C> {
  /// returns a new Counter
  /// ## Arguments
  /// - `value`: big-endian integer represented using 8-bit limbs
  pub fn new(value: [u8; C]) -> Self { Self(value) }

  /// increases counter value by 1 for each new round of `C` byte input.
  ///
  /// ## Note
  /// Returns `max counter reached` error when counter value reaches maximum allowed by different
  /// counter length.
  pub fn increment(&mut self) -> Result<(), String> {
    match C {
      0 => Err("counter value is 0".to_string()),
      _ => {
        // check for max value
        let mut flag = true;
        for value in self.0.iter() {
          if *value != u8::MAX {
            flag = false;
          }
        }

        if flag {
          return Err("max counter reached".to_string());
        }

        let mut add_carry = true;
        for i in (0..C).rev() {
          let (incremented_val, carry) = self.0[i].overflowing_add(add_carry as u8);
          self.0[i] = incremented_val;
          add_carry = carry;
        }

        Ok(())
      },
    }
  }
}

impl<const C: usize> From<usize> for Counter<C> {
  fn from(value: usize) -> Self {
    let mut limbs = [0u8; C];

    let value_bytes = value.to_be_bytes();
    for i in (0..std::cmp::min(C, 8)).rev() {
      limbs[i] = value_bytes[i];
    }

    Self(limbs)
  }
}
