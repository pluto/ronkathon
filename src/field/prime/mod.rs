//! This module contains abstractions specifically for fields of prime order.
//! All the arithmetic operations are implemented for the [`PrimeField`] struct and the
//! [`FiniteField`] trait is implemented. This module asserts at compile time that the order of the
//! field is a prime number and allows for creation of generic prime order fields.

use rand::distributions::{Distribution, Standard};

use super::*;

mod arithmetic;

/// The two prime fields used in the Pluto `ronkathon` system.
pub enum PlutoPrime {
  /// The base field of curves used throughout the system.
  Base = 101,

  /// The scalar field for the curve over the [`PrimeField`] used in the polynomial commitment
  /// scheme.
  Scalar = 17,
}

/// The [`PlutoBaseField`] is a specific instance of the [`PrimeField`] struct with the order set to
/// the prime number `101`. This is the base field used in the Pluto `ronkathon` system.
pub type PlutoBaseField = PrimeField<{ PlutoPrime::Base as usize }>;

/// The [`PlutoScalarField`] is a specific instance of the [`PrimeField`] struct with the order set
/// to the prime number `17`. This is the scalar field used in the Pluto `ronkathon` system.
pub type PlutoScalarField = PrimeField<{ PlutoPrime::Scalar as usize }>;

/// The [`PrimeField`] struct represents elements of a field with prime order. The field is defined
/// by a prime number `P`, and the elements are integers modulo `P`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Default, PartialOrd)]
pub struct PrimeField<const P: usize> {
  value: usize,
}

impl<const P: usize> PrimeField<P> {
  /// Creates a new element of the [`PrimeField`] and will automatically compute the modulus and
  /// return a congruent element between 0 and `P`. Given the `const fn is_prime`, a program that
  /// tries to compile for a non-prime `P` will fail at compile time.
  pub const fn new(value: usize) -> Self {
    is_prime(P);
    Self { value: value % P }
  }
}

impl<const P: usize> const FiniteField for PrimeField<P> {
  const ONE: Self = Self { value: 1 };
  const ORDER: usize = P;
  const PRIMITIVE_ELEMENT: Self = if P == 2 { Self::ONE } else { find_primitive_element::<P>() };
  const ZERO: Self = Self { value: 0 };

  fn inverse(&self) -> Option<Self> {
    if self.value == 0 {
      return None;
    }
    let exponent = Self::ORDER - 2;
    let mut result = Self::ONE;
    let mut base = *self;
    let mut power = exponent;

    while power > 0 {
      if power & 1 == 1 {
        result *= base;
      }
      base = base * base;
      power >>= 1;
    }
    Some(result)
  }

  fn pow(self, power: usize) -> Self {
    if power == 0 {
      Self::ONE
    } else if power == 1 {
      self
    } else if power % 2 == 0 {
      Self::new((self.pow(power / 2).value * self.pow(power / 2).value) % Self::ORDER)
    } else {
      Self::new((self.pow(power / 2).value * self.pow(power / 2).value * self.value) % Self::ORDER)
    }
  }
}

const fn is_prime(n: usize) {
  let mut i = 2;
  while i * i <= n {
    if n % i == 0 {
      panic!("input is not a prime number");
    }
    i += 1;
  }
}

/// This function takes in a prime number `P` and returns a multiplicative generator of the
/// multiplicative group which is typically called a [primitive element](https://en.wikipedia.org/wiki/Primitive_element_(finite_field))
/// of the field. The generator is found by iterating through the numbers from 2 to `P - 1` and
/// checking if the number is a generator of the field.
/// A primitive element `g` of a field `F` is an element such that the powers of `g` generate all
/// the non-zero elements of the field, so we check here that `g` raised to the power of `(P-1)/g`
/// where this division is integer division, is not equal to 1. In other words, we are checking that
/// `g` is coprime to `P-1`. This follows from [Lagrange's theorem](https://en.wikipedia.org/wiki/Lagrange%27s_theorem_(group_theory)).
const fn find_primitive_element<const P: usize>() -> PrimeField<P> {
  let mut i = 2;
  while i * i <= P {
    if (P - 1) % i == 0 {
      if PrimeField::<P>::new(i).pow((P - 1) / i).value != PrimeField::<P>::ONE.value {
        return PrimeField::<P>::new(i);
      } else if PrimeField::<P>::new(P + 1 - i).pow(i).value != PrimeField::<P>::ONE.value {
        return PrimeField::<P>::new(P + 1 - i);
      }
    }
    i += 1;
  }
  panic!("generator not found");
}

impl<const P: usize> fmt::Display for PrimeField<P> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.value) }
}

impl<const P: usize> Distribution<PrimeField<P>> for Standard {
  #[inline]
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> PrimeField<P> {
    loop {
      let next_u31 = (rng.next_u32() >> 4) as usize;
      let is_canonical = next_u31 < PrimeField::<P>::ORDER;
      if is_canonical {
        return PrimeField::<P> { value: next_u31 };
      }
    }
  }
}

impl<const P: usize> From<u32> for PrimeField<P> {
  fn from(val: u32) -> Self { Self::new(val as usize) }
}

impl<const P: usize> From<u64> for PrimeField<P> {
  fn from(val: u64) -> Self { Self::new(val as usize) }
}

impl<const P: usize> From<usize> for PrimeField<P> {
  fn from(val: usize) -> Self { Self::new(val) }
}

impl From<PlutoPrime> for usize {
  fn from(prime: PlutoPrime) -> usize {
    match prime {
      res @ PlutoPrime::Base => res as usize,
      res @ PlutoPrime::Scalar => res as usize,
    }
  }
}

#[cfg(test)]
mod tests {

  use super::*;

  #[rstest]
  #[case(PlutoPrime::Base)]
  #[case(PlutoPrime::Scalar)]
  fn prime_field(#[case] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => {
        PlutoBaseField::new(0);
      },
      PlutoPrime::Scalar => {
        PlutoScalarField::new(0);
      },
    };
  }

  #[test]
  #[should_panic]
  fn non_prime_is_not_finite_field() { let _ = PrimeField::<100>::new(0); }

  fn generator_check<const P: usize>() {
    let g = PrimeField::<P>::PRIMITIVE_ELEMENT;
    let mut counter = 1;
    let mut val = g;
    while val != PrimeField::<P>::ONE {
      val *= g;
      counter += 1;
    }
    assert_eq!(counter, P - 1);
  }

  #[rstest]
  fn generator(#[values(PlutoPrime::Base, PlutoPrime::Scalar)] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => generator_check::<{ PlutoPrime::Base as usize }>(),
      PlutoPrime::Scalar => generator_check::<{ PlutoPrime::Scalar as usize }>(),
    }
  }

  fn zero_check<const P: usize>() {
    assert_eq!(PrimeField::<P>::new(0).value, 0);
    assert_eq!(PrimeField::<P>::new(P).value, 0);
  }

  #[rstest]
  #[case(PlutoPrime::Base)]
  #[case(PlutoPrime::Scalar)]
  fn zero(#[case] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => zero_check::<{ PlutoPrime::Base as usize }>(),
      PlutoPrime::Scalar => zero_check::<{ PlutoPrime::Scalar as usize }>(),
    }
  }

  fn non_zero_check<const P: usize>() {
    let a = PrimeField::<P>::new(10);
    assert!(!(a == PrimeField::<P>::ZERO));
  }

  #[rstest]
  #[case(PlutoPrime::Base)]
  #[case(PlutoPrime::Scalar)]
  fn non_zero(#[case] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => non_zero_check::<{ PlutoPrime::Base as usize }>(),
      PlutoPrime::Scalar => non_zero_check::<{ PlutoPrime::Scalar as usize }>(),
    }
  }

  fn identity_elements_check<const P: usize>() {
    let zero = PrimeField::<P>::new(0);
    let one = PrimeField::<P>::new(1);
    for i in 0..PrimeField::<P>::ORDER {
      let f = PrimeField::<P>::new(i);
      assert_eq!(f + zero, f);
      assert_eq!(f * one, f);
      assert_eq!(f * zero, zero);
    }
  }

  #[rstest]
  #[case(PlutoPrime::Base)]
  #[case(PlutoPrime::Scalar)]
  fn identity_elements(#[case] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => identity_elements_check::<{ PlutoPrime::Base as usize }>(),
      PlutoPrime::Scalar => identity_elements_check::<{ PlutoPrime::Scalar as usize }>(),
    }
  }

  fn inverse_of_inverse_check<const P: usize>() {
    for i in 1..PrimeField::<P>::ORDER {
      let a = PrimeField::<P>::new(i);
      let a_inv = a.inverse().unwrap();
      let a_inv_inv = a_inv.inverse().unwrap();
      assert_eq!(a_inv_inv, a);
    }
  }

  #[rstest]
  #[case(PlutoPrime::Base)]
  #[case(PlutoPrime::Scalar)]
  fn inverse_of_inverse(#[case] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => inverse_of_inverse_check::<{ PlutoPrime::Base as usize }>(),
      PlutoPrime::Scalar => inverse_of_inverse_check::<{ PlutoPrime::Scalar as usize }>(),
    }
  }

  #[should_panic]
  #[test]
  fn not_primitive_root_of_unity() {
    let n = 3;
    let _root = PlutoScalarField::primitive_root_of_unity(n);
  }
}
