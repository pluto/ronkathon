//! Hash based commitment scheme.
//!
//! To commit to a message `m`, pick 32 random bytes `r` and publish `c = H(r || m)`. To open,
//! reveal `m` and `r`, and anyone can recompute the hash.
//!
//! - Hiding: `r` is random, so `c` reveals nothing about `m`, even when there are only a few
//!   possible messages. Without `r`, anyone could hash every candidate and compare.
//! - Binding: opening `c` to a different message would need a second preimage or a collision of
//!   `H`.
use rand::Rng;

use super::CommitmentScheme;
use crate::hashes::sha::Sha256;

/// Number of random bytes used to hide the message.
pub const RANDOMNESS_LEN: usize = 32;

/// Commitment `SHA256(r || m)` to a message `m` of any length, with random bytes `r`.
///
/// ## Example
/// ```
/// use rand::thread_rng;
/// use ronkathon::commitments::{hash::HashCommitment, CommitmentScheme};
///
/// let scheme = HashCommitment;
/// let message = b"heads".to_vec();
///
/// let (commitment, opening) = scheme.commit(&message, &mut thread_rng());
/// // ...later, `message` and `opening` are revealed
/// assert!(scheme.verify(&commitment, &message, &opening));
/// assert!(!scheme.verify(&commitment, &b"tails".to_vec(), &opening));
/// ```
#[derive(Debug, Clone, Copy, Default)]
pub struct HashCommitment;

impl HashCommitment {
  fn hash(message: &[u8], randomness: &[u8; RANDOMNESS_LEN]) -> Vec<u8> {
    let input = [randomness.as_slice(), message].concat();
    Sha256::new().digest(&input)
  }
}

impl CommitmentScheme for HashCommitment {
  type Commitment = Vec<u8>;
  type Message = Vec<u8>;
  type Opening = [u8; RANDOMNESS_LEN];

  fn commit<R: Rng + ?Sized>(
    &self,
    message: &Self::Message,
    rng: &mut R,
  ) -> (Self::Commitment, Self::Opening) {
    let randomness: [u8; RANDOMNESS_LEN] = rng.gen();
    (Self::hash(message, &randomness), randomness)
  }

  fn verify(
    &self,
    commitment: &Self::Commitment,
    message: &Self::Message,
    opening: &Self::Opening,
  ) -> bool {
    Self::hash(message, opening) == *commitment
  }
}

#[cfg(test)]
mod tests {
  use rand::thread_rng;

  use super::*;

  #[test]
  fn opens_to_committed_message() {
    let scheme = HashCommitment;
    for message in [Vec::new(), b"a".to_vec(), vec![0xab; 1000]] {
      let (commitment, opening) = scheme.commit(&message, &mut thread_rng());
      assert!(scheme.verify(&commitment, &message, &opening));
    }
  }

  #[test]
  fn rejects_other_message_or_opening() {
    let scheme = HashCommitment;
    let message = b"heads".to_vec();
    let (commitment, opening) = scheme.commit(&message, &mut thread_rng());

    assert!(!scheme.verify(&commitment, &b"tails".to_vec(), &opening));

    let mut other_opening = opening;
    other_opening[0] ^= 1;
    assert!(!scheme.verify(&commitment, &message, &other_opening));
  }

  /// Committing to the same message twice gives different commitments, so they don't reveal
  /// that the messages are equal.
  #[test]
  fn same_message_different_commitments() {
    let scheme = HashCommitment;
    let message = b"heads".to_vec();
    let (first, _) = scheme.commit(&message, &mut thread_rng());
    let (second, _) = scheme.commit(&message, &mut thread_rng());
    assert_ne!(first, second);
  }
}
