//! This module contains the [`ExtensionField`] trait and the [`GaloisField`] struct that represents
//! elements of an extension field. The extension field is constructed by adjoining the roots of a
//! polynomial to the original field via the [`ExtensionField::IRREDUCIBLE_POLYNOMIAL_COEFFS`]
//! array.
//!
//! This is still a work in progress to push towards a more generic implementation as the current
//! still requires that specific irreducibles are given in order to construct the extension, though
//! it should be possible to construct the extension at compile time.

use std::array;

use super::{prime::*, *};

mod arithmetic;
pub mod gf_101_2;
pub mod gf_2_8;

/// The [`PlutoBaseFieldExtension`] is a specific instance of the [`GaloisField`] struct with the
/// order set to the prime number `101^2`. This is the quadratic extension field over the
/// [`PlutoBaseField`] used in the Pluto `ronkathon` system.
pub type PlutoBaseFieldExtension = GaloisField<2, 101>;

/// The [`AESFieldExtension`] is a specific instance of the [`GaloisField`] struct with the
/// order set to the number `2^8`. This is the quadratic extension field over the
/// [`AESField`][crate::field::prime::AESField] used in the Pluto `ronkathon` system.
pub type AESFieldExtension = GaloisField<8, 2>;

/// The [`PlutoScalarFieldExtension`] is a specific instance of the [`GaloisField`] struct with the
/// order set to the prime number `17^2`. This is the quadratic extension field over the
/// [`field::prime::PlutoScalarField`] used in the Pluto `ronkathon` system.
pub type PlutoScalarFieldExtension = GaloisField<2, { PlutoPrime::Scalar as usize }>;

/// Sizes of the fields for extensions on the [`PlutoPrime`]s.
pub enum PlutoExtensions {
  /// The size of the quadratic extension field over the [`PlutoPrime::Base`] field.
  QuadraticBase = 101 * 101,
  /// The size of the quadratic extension field over the [`PlutoPrime::Scalar`] field.
  QuadraticScalar = 17 * 17,
}

/// A field extension is a field that contains the original field and additional elements that are
/// not in the original field. The extension field is constructed by adjoining the roots of a
/// polynomial to the original field.
#[const_trait]
pub trait ExtensionField<const N: usize, const P: usize>:
  Field
  + From<PrimeField<P>>
  + Add<PrimeField<P>, Output = Self>
  + AddAssign<PrimeField<P>>
  + Sub<PrimeField<P>, Output = Self>
  + SubAssign<PrimeField<P>>
  + Mul<PrimeField<P>, Output = Self>
  + MulAssign<PrimeField<P>>
where [PrimeField<P>; N + 1]: {
  /// The coefficients of the irreducible polynomial used to reduce field polynomials to the
  /// desired degree.
  const IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS: [PrimeField<P>; N + 1];
}

/// A struct that represents an element of an extension field. The element is represented as
/// [`Monomial`] coefficients of a [`Polynomial`] of degree `N - 1` over the base [`FiniteField`]
/// `F`.
#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Hash, Debug)]
pub struct GaloisField<const N: usize, const P: usize> {
  pub(crate) coeffs: [PrimeField<P>; N],
}

impl<const N: usize, const P: usize> Finite for GaloisField<N, P> {
  const ORDER: usize = PrimeField::<P>::ORDER.pow(N as u32);
}

// impl<const N: usize, const P: usize> FiniteField for GaloisField<N, P> {
//   const GENERATOR: Self = panic!();
//   const NEG_ONE: Self = Self::new(single_instance_array(PrimeField::<P>::NEG_ONE));
//   const ONE: Self = Self::new(single_instance_array(PrimeField::<P>::ONE));
//   const ORDER: usize = P.pow(N as usize) as usize;
//   const THREE: Self = Self::new(single_instance_array(PrimeField::<P>::THREE));
//   const TWO: Self = Self::new(single_instance_array(PrimeField::<P>::from(2usize)));
//   const ZERO: Self = Self::new([PrimeField::<P>::ZERO; N]);

//   fn inverse(&self) -> Option<Self> { todo!() }

//   fn pow(self, power: usize) -> Self { todo!() }
// }

// TODO: This is useful for generating arrays at const time
// const fn single_instance_array<const N: usize, const P: usize>(
//   value: PrimeField<P>,
// ) -> [PrimeField<P>; N] {
//   let mut arr = [PrimeField::<P>::ZERO; N];
//   arr[0] = value;
//   arr
// }

// TODO: We could get the irreducible polynomial with const fn
/// A polynomial is irreducible if `x^(p^q) - x` is divisible by the polynomial.
// const fn get_irreducible_poly<const N: usize, const P: usize>() -> [PrimeField<P>; N + 1]
// where [(); P as usize * N + 1]: {
//   // Make our polynomial x^(p^q) - x
//   let mut divisible = [PrimeField::<P>::ZERO; P as usize * N + 1];
//   divisible[1] = PrimeField::<P>::NEG_ONE;
//   divisible[P as usize * N] = PrimeField::<P>::ONE;
//   let divisible = Polynomial::<Monomial, PrimeField<P>>::from(divisible);

//   let mut poly = Polynomial::<Monomial, PrimeField<P>>::from([PrimeField::<P>::ZERO; N + 1]);

//   for i in 0..N + 1 {
//     for j in 0..P as usize * i {
//       poly.coefficients[j / i] = PrimeField::<P>::new((j % i) as usize);
//       if divisible.clone() % poly.clone()
//         == Polynomial::<Monomial, PrimeField<P>>::from([PrimeField::<P>::ZERO; 1])
//       {
//         return array::from_fn(|i| {
//           poly.coefficients.get(i).cloned().unwrap_or(PrimeField::<P>::ZERO)
//         });
//       }
//     }
//   }
//   panic!();
// }

// ADDED THIS IN HERE FOR CONST GENERATOR
// const fn remainder<const N: usize, const P: u32>(
//   lhs: [PrimeField<P>; N * P as usize + 1],
//   rhs: [PrimeField<P>; N],
// ) -> [PrimeField<P>; N] {
//   // Initial quotient value
//   let mut q = [PrimeField::<P>::ZERO; N];

//   // Initial remainder value is our numerator polynomial
//   let mut p = [PrimeField::<P>::ZERO; N * P as usize + 1];

//   // Leading coefficient of the denominator
//   let c = rhs.leading_coefficient();

//   // Create quotient polynomial
//   let mut diff = p.degree() as isize - rhs.degree() as isize;
//   if diff < 0 {
//     return (Self::new(vec![F::ZERO]), p);
//   }
//   let mut q_coeffs = vec![F::ZERO; diff as usize + 1];

//   // Perform the repeated long division algorithm
//   while diff >= 0 {
//     let s = p.leading_coefficient() * c.inverse().unwrap();
//     q_coeffs[diff as usize] = s;
//     p -= rhs.pow_mult(s, diff as usize);
//     p.trim_zeros();
//     diff = p.degree() as isize - rhs.degree() as isize;
//   }
//   q.coefficients = q_coeffs;
//   (q, p)
// }

impl<const N: usize, const P: usize> Default for GaloisField<N, P> {
  fn default() -> Self { Self { coeffs: [PrimeField::<P>::ZERO; N] } }
}

impl<const N: usize, const P: usize> GaloisField<N, P> {
  /// Create a new extension field element from the given coefficients of the field in polynomial
  /// form. The coefficients are expected to be from [`FiniteField`] you are extending over in the
  /// order of increasing degree. For example, for a quadratic (`N=2`) extension field, the
  /// coefficients are `[a, b]` where `a + b * t`.
  pub const fn new(coeffs: [PrimeField<P>; N]) -> Self { Self { coeffs } }
}

/// Convert from a [`FiniteField`] element into the [`GaloisField`] field element in the natural
/// way.
impl<const N: usize, const P: usize> From<PrimeField<P>> for GaloisField<N, P> {
  fn from(value: PrimeField<P>) -> Self {
    let mut coeffs = [PrimeField::<P>::ZERO; N];
    coeffs[0] = value;
    Self { coeffs }
  }
}

/// Convert from a [`u32`] into the [`GaloisField`] field element in the natural way.
impl<const N: usize, const P: usize> From<u32> for GaloisField<N, P> {
  fn from(val: u32) -> Self { Self::from(PrimeField::<P>::from(val)) }
}

/// Convert from a [`u64`] into the [`GaloisField`] field element in the natural way.
impl<const N: usize, const P: usize> From<u64> for GaloisField<N, P> {
  fn from(val: u64) -> Self { Self::from(PrimeField::<P>::from(val)) }
}

/// Convert from a [`usize`] into the [`GaloisField`] field element in the natural way.
impl<const N: usize, const P: usize> From<usize> for GaloisField<N, P> {
  fn from(val: usize) -> Self { Self::from(PrimeField::<P>::from(val)) }
}

impl<const N: usize, const P: usize> From<GaloisField<N, P>> for usize {
  fn from(value: GaloisField<N, P>) -> Self { value.coeffs[0].value }
}
