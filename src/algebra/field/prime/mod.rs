//! This module contains abstractions specifically for fields of prime order.
//! All the arithmetic operations are implemented for the [`PrimeField`] struct and the
//! [`FiniteField`] trait is implemented. This module asserts at compile time that the order of the
//! field is a prime number and allows for creation of generic prime order fields.

use std::{fmt, str::FromStr};

use rand::{distributions::Standard, prelude::Distribution, Rng};

use super::*;
use crate::algebra::Finite;

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

/// The [`AESField`] is just a field over the prime 2, used within
/// [`AES`][crate::encryption::symmetric::aes]
pub type AESField = PrimeField<2>;

/// The [`PrimeField`] struct represents elements of a field with prime order. The field is defined
/// by a prime number `P`, and the elements are integers modulo `P`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Default, PartialOrd)]
pub struct PrimeField<const P: usize> {
  pub(crate) value: usize,
}

impl<const P: usize> PrimeField<P> {
  /// Creates a new element of the [`PrimeField`] and will automatically compute the modulus and
  /// return a congruent element between 0 and `P`. Given the `const fn is_prime`, a program that
  /// tries to compile for a non-prime `P` will fail at compile time.
  pub const fn new(value: usize) -> Self {
    is_prime(P);
    Self { value: value % P }
  }

  /// Computes euler criterion of the field element, i.e. Returns true if the element is a quadratic
  /// residue (a square number) in the field.
  ///
  /// ## NOTES
  /// By fermat's little theorem, (assume `is_congruent_to` is =)
  ///     x^(p-1) - 1 = 0 mod P
  ///
  /// All primes > 2 are odd, a.k.a P is odd, hence (P-1) is even.
  /// So, we can split as follows:
  ///     (x^(p-1)/2 - 1)(x^(p-1)/2 + 1) = 0 mod P
  /// or       L        *     R          = 0 mod P
  ///
  /// All quadratic residues are of the form (g^(2k)) where `g` is the
  /// multiplicative generator and k is some natural number. All non-residues
  /// on the other hand are of the form (g^(2k+1)).
  ///
  /// In case of QR, substitute x = g^2k
  ///     g^(2k)((p-1)/2) = 1 mod P
  ///     g^(p-1) = 1 mod P
  /// which is true by fermat's little theorem
  ///
  /// In the other case, the same doesn't hold.
  /// Hence, the case `L` should hold for all quadratic residues and is the
  /// test for quadratic residuosity.
  ///
  /// More info here: https://www.youtube.com/watch?v=2IBPOI43jek
  pub fn euler_criterion(&self) -> bool { self.pow((P - 1) / 2).value == 1 }

  /// Computes the square root of a field element using the [Tonelli-Shanks algorithm](https://en.wikipedia.org/wiki/Tonelli–Shanks_algorithm).
  pub fn sqrt(&self) -> Option<(Self, Self)> {
    if *self == Self::ZERO {
      return Some((Self::ZERO, Self::ZERO));
    }

    assert!(self.euler_criterion(), "Element is not a quadratic residue");

    // First define the Q and S values for the prime number P.
    let q: usize;
    let mut s = 1;
    loop {
      let lhs = P - 1;
      let rhs = 2_usize.pow(s);
      let check_value = lhs % rhs;
      if check_value == 0 {
        s += 1;
      } else {
        s -= 1;
        q = (P - 1) / 2_usize.pow(s);
        break;
      }
    }

    // Find a z that is not a quadratic residue
    let mut z = Self::new(2);
    while z.euler_criterion() {
      z += Self::ONE;
    }
    let mut m = s;
    let mut c = z.pow(q);
    let mut t = self.pow(q);
    let mut r = self.pow((q + 1) / 2);
    loop {
      if t == Self::ONE {
        if -r < r {
          return Some((-r, r));
        } else {
          return Some((r, -r));
        }
      }
      // Repeatedly square to find a t^2^i = 1
      let mut i = 1;
      let mut t_pow = t.pow(2);
      while t_pow != Self::ONE {
        t_pow = t_pow.pow(2);
        i += 1;
      }
      let b = c.pow(2_usize.pow(m - i - 1));
      m = i;
      c = b.pow(2);
      t *= c;
      r *= b;
    }
  }
}

impl<const P: usize> const Finite for PrimeField<P> {
  const ORDER: usize = P;
}

impl<const P: usize> const Field for PrimeField<P> {
  const ONE: Self = Self { value: 1 };
  const ZERO: Self = Self { value: 0 };

  fn inverse(&self) -> Option<Self> {
    if self.value == 0 {
      return None;
    }

    // By fermat's little theorem, in any prime field P, for any elem:
    //    e^(P-1) = 1 mod P
    // So,
    //    e^(P-2) = e^-1 mod P
    Some(self.pow(Self::ORDER - 2))
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

impl<const P: usize> FiniteField for PrimeField<P> {
  const PRIMITIVE_ELEMENT: Self =
    if P == 2 { Self::ONE } else { Self::new(find_primitive_element::<P>()) };
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
pub const fn find_primitive_element<const P: usize>() -> usize {
  let mut i = 2;
  while i * i <= P {
    if (P - 1) % i == 0 {
      if PrimeField::<P>::new(i).pow((P - 1) / i).value != PrimeField::<P>::ONE.value {
        return i;
      } else if PrimeField::<P>::new(P + 1 - i).pow(i).value != PrimeField::<P>::ONE.value {
        return P + 1 - i;
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

impl<const P: usize> From<PrimeField<P>> for usize {
  fn from(value: PrimeField<P>) -> Self { value.value }
}

impl<const P: usize> From<i32> for PrimeField<P> {
  fn from(value: i32) -> Self {
    let abs = Self::new(value.unsigned_abs() as usize);
    if value.is_positive() {
      abs
    } else {
      -abs
    }
  }
}

impl<const P: usize> FromStr for PrimeField<P> {
  type Err = ();

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    let num = str::parse(s).expect("failed to parse string into usize");
    Ok(Self::new(num))
  }
}

#[cfg(test)]
mod tests {

  use rstest::rstest;

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

  // The quadratic residues over GF(101) are:
  // [1, 4, 5, 6, 9, 13, 14, 16, 17, 19, 20, 21, 22, 23, 24, 25, 30, 31, 33, 36, 37, 43, 45, 47, 49,
  // 52, 54, 56, 58, 64, 65, 68, 70, 71, 76, 77, 78, 79, 80, 81, 82, 84, 85, 87, 88, 92, 95, 96, 97,
  // 100]
  #[rstest]
  // This first test case will panic because 2 is not a primitive root of unity for the scalar
  // field, so the expected value is irrelevant.
  #[should_panic]
  #[case(PlutoBaseField::new(2), (PlutoBaseField::new(69420), PlutoBaseField::new(69420)))]
  #[case(PlutoBaseField::new(4), (PlutoBaseField::new(2), PlutoBaseField::new(99)))]
  #[case(PlutoBaseField::new(5), (PlutoBaseField::new(45), PlutoBaseField::new(56)))]
  #[case(PlutoBaseField::new(6), (PlutoBaseField::new(39), PlutoBaseField::new(62)))]
  #[case(PlutoBaseField::new(0), (PlutoBaseField::new(0), PlutoBaseField::new(0)))]
  fn square_root(#[case] a: PlutoBaseField, #[case] expected: (PlutoBaseField, PlutoBaseField)) {
    assert_eq!(a.sqrt().unwrap(), expected);
  }
}
