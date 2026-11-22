//! Pedersen commitment scheme over an elliptic curve.
//!
//! To commit to a scalar `m`, pick a random scalar `r` and publish the point `C = m·G + r·H`,
//! where `G` and `H` are two generators of the same group. To open, reveal `m` and `r`.
//!
//! - Hiding: `r·H` is a uniformly random group element, so `C` reveals nothing about `m`, even to
//!   someone with unbounded computing power.
//! - Binding: opening `C` to a different message needs the discrete log of `H` with respect to `G`.
//!   With `H = h·G` known, `C = (m + r·h)·G` opens to any `m'` with `r' = r + (m - m') / h`.
//!
//! Commitments are additively homomorphic: `commit(m₁, r₁) + commit(m₂, r₂)` is a commitment to
//! `m₁ + m₂` with opening `r₁ + r₂`.
//!
//! **Note**: the subgroup of the Pluto curves only has 17 elements, so discrete logs are trivial
//! to find and this is only for learning.
use rand::Rng;

use super::CommitmentScheme;
use crate::{
  algebra::{field::Field, group::FiniteCyclicGroup, Finite},
  curve::{AffinePoint, EllipticCurve},
};

/// Pedersen commitment `C = m·G + r·H` to a scalar `m` of the curve `C`.
///
/// ## Example
/// ```
/// use rand::thread_rng;
/// use ronkathon::{
///   algebra::field::prime::PlutoScalarField,
///   commitments::{pedersen::PedersenCommitment, CommitmentScheme},
///   curve::pluto_curve::PlutoBaseCurve,
/// };
///
/// let mut rng = thread_rng();
/// let scheme = PedersenCommitment::<PlutoBaseCurve>::new(&mut rng);
///
/// let (first, first_opening) = scheme.commit(&PlutoScalarField::new(3), &mut rng);
/// let (second, second_opening) = scheme.commit(&PlutoScalarField::new(5), &mut rng);
///
/// // the sum of the commitments is a commitment to the sum of the messages
/// assert!(scheme.verify(
///   &(first + second),
///   &PlutoScalarField::new(8),
///   &(first_opening + second_opening)
/// ));
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PedersenCommitment<C: EllipticCurve> {
  g: AffinePoint<C>,
  h: AffinePoint<C>,
}

/// A uniformly random scalar of the curve `C`.
fn random_scalar<C: EllipticCurve, R: Rng + ?Sized>(rng: &mut R) -> C::ScalarField {
  C::ScalarField::from(rng.gen_range(0..C::ScalarField::ORDER))
}

impl<C: EllipticCurve> PedersenCommitment<C> {
  /// Uses the curve generator as `G` and a random multiple of it as `H`, then forgets the
  /// multiple. This stands in for a trusted setup, or for hashing to the curve so that nobody
  /// ever knows the discrete log of `H`.
  pub fn new<R: Rng + ?Sized>(rng: &mut R) -> Self {
    let g = AffinePoint::<C>::GENERATOR;
    let mut h_log = random_scalar::<C, R>(rng);
    while h_log == C::ScalarField::ZERO {
      h_log = random_scalar::<C, R>(rng);
    }
    Self { g, h: g * h_log }
  }

  /// Uses the given generators. Binding only holds if nobody knows the discrete log of `h` with
  /// respect to `g`.
  pub fn from_generators(g: AffinePoint<C>, h: AffinePoint<C>) -> Self { Self { g, h } }
}

impl<C: EllipticCurve> CommitmentScheme for PedersenCommitment<C> {
  type Commitment = AffinePoint<C>;
  type Message = C::ScalarField;
  type Opening = C::ScalarField;

  fn commit<R: Rng + ?Sized>(
    &self,
    message: &Self::Message,
    rng: &mut R,
  ) -> (Self::Commitment, Self::Opening) {
    let randomness = random_scalar::<C, R>(rng);
    (self.g * *message + self.h * randomness, randomness)
  }

  fn verify(
    &self,
    commitment: &Self::Commitment,
    message: &Self::Message,
    opening: &Self::Opening,
  ) -> bool {
    self.g * *message + self.h * *opening == *commitment
  }
}

#[cfg(test)]
mod tests {
  use rand::thread_rng;

  use super::*;
  use crate::{algebra::field::prime::PlutoScalarField, curve::pluto_curve::PlutoBaseCurve};

  type Pedersen = PedersenCommitment<PlutoBaseCurve>;

  #[test]
  fn opens_to_committed_message() {
    let mut rng = thread_rng();
    let scheme = Pedersen::new(&mut rng);
    for value in 0..17 {
      let message = PlutoScalarField::new(value);
      let (commitment, opening) = scheme.commit(&message, &mut rng);
      assert!(scheme.verify(&commitment, &message, &opening));
      assert!(!scheme.verify(&commitment, &(message + PlutoScalarField::ONE), &opening));
    }
  }

  #[test]
  fn additively_homomorphic() {
    let mut rng = thread_rng();
    let scheme = Pedersen::new(&mut rng);
    let (m1, m2) = (PlutoScalarField::new(4), PlutoScalarField::new(15));
    let (c1, r1) = scheme.commit(&m1, &mut rng);
    let (c2, r2) = scheme.commit(&m2, &mut rng);
    assert!(scheme.verify(&(c1 + c2), &(m1 + m2), &(r1 + r2)));
  }

  /// Shows why the discrete log of `H` has to stay unknown: whoever knows it can open a
  /// commitment to any message.
  #[test]
  fn known_discrete_log_breaks_binding() {
    let mut rng = thread_rng();
    let g = AffinePoint::<PlutoBaseCurve>::GENERATOR;
    let h_log = PlutoScalarField::new(7);
    let scheme = Pedersen::from_generators(g, g * h_log);

    let message = PlutoScalarField::new(3);
    let (commitment, opening) = scheme.commit(&message, &mut rng);

    let other_message = PlutoScalarField::new(11);
    let other_opening = opening + (message - other_message) / h_log;
    assert!(scheme.verify(&commitment, &other_message, &other_opening));
  }
}
