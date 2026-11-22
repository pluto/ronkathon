//! Commitment schemes.
//!
//! A commitment scheme lets a party commit to a message now and reveal it later, so that the
//! commitment hides the message until the reveal (*hiding*) and can't be opened to a different
//! message afterwards (*binding*).
//!
//! - [`hash::HashCommitment`]: commits to bytes with a hash of the message and random bytes.
//! - [`pedersen::PedersenCommitment`]: commits to a scalar as a point on an elliptic curve, and is
//!   additively homomorphic.
use rand::Rng;

pub mod hash;
pub mod pedersen;

/// A scheme to commit to a [`CommitmentScheme::Message`] and later prove what the message was.
///
/// The committer calls [`CommitmentScheme::commit`], publishes the commitment and keeps the
/// opening. To reveal, they publish the message and the opening, and anyone can check them against
/// the commitment with [`CommitmentScheme::verify`].
pub trait CommitmentScheme {
  /// What gets committed to.
  type Message;
  /// The value that is published at commit time.
  type Commitment;
  /// The secret randomness used to commit, revealed together with the message.
  type Opening;

  /// Commits to `message`, using `rng` for the randomness that hides it.
  ///
  /// Returns the commitment to publish, and the opening to keep until the message is revealed.
  fn commit<R: Rng + ?Sized>(
    &self,
    message: &Self::Message,
    rng: &mut R,
  ) -> (Self::Commitment, Self::Opening);

  /// Checks that `commitment` is a commitment to `message` with `opening`.
  fn verify(
    &self,
    commitment: &Self::Commitment,
    message: &Self::Message,
    opening: &Self::Opening,
  ) -> bool;
}
