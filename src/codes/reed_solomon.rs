//! This contains an implementation of the Reed-Solomon error correction code.

use std::array;

use itertools::Itertools;

use super::*;
use crate::algebra::field::FiniteField;

// TODO: We should allow for arbitrary data in the message so long as it can be
// converted into an element of a prime field and decoded the same way.

/// Represents a message that is to be encoded or decoded using the Reed-Solomon algorithm.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Message<const K: usize, const P: usize> {
  /// The data that is to be encoded.
  pub data: [PrimeField<P>; K],
}

/// A [`Codeword`] is a message that has been encoded using the Reed-Solomon algorithm.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Codeword<const N: usize, const K: usize, const P: usize> {
  /// The data that has been encoded.
  pub data: [Coordinate<N, P>; N],
}

/// A [`Coordinate`] represents a point on a polynomial curve with both the x and y coordinates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Coordinate<const N: usize, const P: usize> {
  /// The x-coordinate of the point.
  pub x: PrimeField<P>,

  /// The y-coordinate of the point.
  pub y: PrimeField<P>,
}

impl<const K: usize, const P: usize> Message<K, P> {
  /// Creates a new message from the given data.
  pub fn new(data: [PrimeField<P>; K]) -> Self { Self { data } }

  /// Encodes the message into a [`Codeword`].
  pub fn encode<const N: usize>(self) -> Codeword<N, K, P> {
    assert_ge::<N, K>();
    let primitive_root = PrimeField::<P>::primitive_root_of_unity(N);
    let polynomial = Polynomial::from(self);
    Codeword {
      data: array::from_fn(|pow| Coordinate {
        x: primitive_root.pow(pow),
        y: polynomial.evaluate(primitive_root.pow(pow)),
      }),
    }
  }

  /// Decodes the message from a [`Codeword`].
  pub fn decode<const M: usize>(codeword: Codeword<M, K, P>) -> Self {
    assert_ge::<M, K>();
    let x_values: [PrimeField<P>; K] = {
      let mut array = [PrimeField::<P>::ZERO; K];
      for (i, x) in codeword.data.iter().map(|c| c.x).take(K).enumerate() {
        array[i] = x;
      }
      array
    };

    let y_values: [PrimeField<P>; K] = {
      let mut array = [PrimeField::<P>::ZERO; K];
      for (i, y) in codeword.data.iter().map(|c| c.y).take(K).enumerate() {
        array[i] = y;
      }
      array
    };

    let mut data = [PrimeField::<P>::ZERO; K];

    #[allow(clippy::needless_range_loop)]
    // i is the degree of the monomial.
    for i in 0..K {
      for j in 0..K {
        let x_combinations: PrimeField<P> = if i % 2 == 1 {
          PrimeField::<P>::ZERO - PrimeField::<P>::ONE
        } else {
          PrimeField::<P>::ONE
        } * x_values
          .iter()
          .enumerate()
          .filter(|&(index, _)| index != j)
          .map(|(_, x)| x)
          .combinations(K - 1 - i)
          .map(|comb| comb.into_iter().copied().product::<PrimeField<P>>())
          .sum::<PrimeField<P>>();
        let y_combinations = y_values[j];
        let numerator = x_combinations * y_combinations;

        // this could be put into the x_combinations iter above.
        let mut denominator = PrimeField::ONE; // x_values[i];
        for k in 0..K {
          if k == j {
            continue;
          }
          denominator *= x_values[k] - x_values[j];
        }

        data[i] += numerator / denominator;
      }
    }
    Message { data }
  }
}

const fn assert_ge<const N: usize, const K: usize>() {
  assert!(N >= K, "Code size must be greater than or equal to K");
}

impl<const K: usize, const P: usize> From<Message<K, P>>
  for Polynomial<Monomial, PrimeField<P>, K>
{
  fn from(message: Message<K, P>) -> Self { Polynomial::from(message.data) }
}

#[cfg(test)]
mod tests {

  // NOTES: When we encode a message to same length, we get the first index correct when we decode.
  // Otherwise we are getting the last correct.
  use super::*;

  // A mersenne prime because why not.
  const P: usize = 127;

  // Message size.
  const K: usize = 3;

  // Codeword size which satisfies (127-1) % 7 == 0, so we have roots of unity.
  const N: usize = 7;

  #[test]
  fn encode_same_size() {
    // Creat the message from an array using our constants above.
    let mut arr = [PrimeField::<P>::ZERO; K];
    arr[0] = PrimeField::<P>::new(1);
    arr[1] = PrimeField::<P>::new(2);
    arr[2] = PrimeField::<P>::new(3);
    let message = Message::new(arr);

    // Build the codeword from the message.
    let codeword = message.encode::<K>();
    assert_eq!(codeword.data.len(), K);
    assert_eq!(codeword.data[0].x, PrimeField::<P>::new(1));
    assert_eq!(codeword.data[1].x, PrimeField::<P>::new(107));
    assert_eq!(codeword.data[2].x, PrimeField::<P>::new(19));
    assert_eq!(codeword.data[0].y, PrimeField::<P>::new(6));
    assert_eq!(codeword.data[1].y, PrimeField::<P>::new(18));
    assert_eq!(codeword.data[2].y, PrimeField::<P>::new(106));
  }

  #[test]
  fn encode_larger_size() {
    // Creat the message from an array using our constants above.
    let mut arr = [PrimeField::<P>::ZERO; K];
    arr[0] = PrimeField::<P>::new(1);
    arr[1] = PrimeField::<P>::new(2);
    arr[2] = PrimeField::<P>::new(3);
    let message = Message::new(arr);

    // Build the codeword from the message.
    let codeword = message.encode::<K>();
    assert_eq!(codeword.data.len(), K);
    assert_eq!(codeword.data[0].x, PrimeField::<P>::new(1));
    assert_eq!(codeword.data[1].x, PrimeField::<P>::new(107));
    assert_eq!(codeword.data[2].x, PrimeField::<P>::new(19));
    assert_eq!(codeword.data[0].y, PrimeField::<P>::new(6));
    assert_eq!(codeword.data[1].y, PrimeField::<P>::new(18));
    assert_eq!(codeword.data[2].y, PrimeField::<P>::new(106));
  }

  #[test]
  fn decoding() {
    // Creat the message from an array using our constants above.
    let mut arr = [PrimeField::<P>::ZERO; K];
    arr[0] = PrimeField::<P>::new(1);
    arr[1] = PrimeField::<P>::new(2);
    arr[2] = PrimeField::<P>::new(3);
    let message = Message::new(arr);

    // Build the codeword from the message.
    let codeword = message.encode::<N>();

    // Decode the codeword back into a message.
    let decoded = Message::decode::<N>(codeword);

    assert_eq!(decoded.data[0], PrimeField::<P>::new(1));
    assert_eq!(decoded.data[1], PrimeField::<P>::new(2));
    assert_eq!(decoded.data[2], PrimeField::<P>::new(3));
  }

  #[test]
  fn decoding_longer_message() {
    // Creat the message from an array using our constants above.
    let mut arr = [PrimeField::<P>::ZERO; 5];
    arr[0] = PrimeField::<P>::new(1);
    arr[1] = PrimeField::<P>::new(2);
    arr[2] = PrimeField::<P>::new(3);
    arr[3] = PrimeField::<P>::new(4);
    arr[4] = PrimeField::<P>::new(5);
    let message = Message::new(arr);

    // Build the codeword from the message.
    let codeword = message.encode::<N>();

    // Decode the codeword back into a message.
    let decoded = Message::decode::<N>(codeword);

    assert_eq!(decoded.data[0], PrimeField::<P>::new(1));
    assert_eq!(decoded.data[1], PrimeField::<P>::new(2));
    assert_eq!(decoded.data[2], PrimeField::<P>::new(3));
    assert_eq!(decoded.data[3], PrimeField::<P>::new(4));
    assert_eq!(decoded.data[4], PrimeField::<P>::new(5));
  }
}
