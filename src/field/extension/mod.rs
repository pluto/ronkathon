use super::*;

mod arithmetic;
pub mod gf_101_2;

/// A field extension is a field that contains the original field and additional elements that are
/// not in the original field. The extension field is constructed by adjoining the roots of a
/// polynomial to the original field.
#[const_trait]
pub trait ExtensionField<const N: usize, const P: u32>:
  FiniteField
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
  const IRREDUCIBLE_POLYNOMIAL_COEFFS: [PrimeField<P>; N + 1];
}

/// A struct that represents an element of an extension field. The element is represented as
/// [`Monomial`] coefficients of a [`Polynomial`] of degree `N - 1` over the base [`FiniteField`]
/// `F`.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
pub struct GaloisField<const N: usize, const P: u32> {
  pub(crate) coeffs: [PrimeField<P>; N],
}

// impl<const N: usize, const P: u32> FiniteField for GaloisField<N, P> {
//   const GENERATOR: Self = panic!();
//   const NEG_ONE: Self = Self::new(single_instance_array(PrimeField::<P>::NEG_ONE));
//   const ONE: Self = Self::new(single_instance_array(PrimeField::<P>::ONE));
//   const ORDER: u32 = P.pow(N as u32) as u32;
//   const THREE: Self = Self::new(single_instance_array(PrimeField::<P>::THREE));
//   const TWO: Self = Self::new(single_instance_array(PrimeField::<P>::from(2u32)));
//   const ZERO: Self = Self::new([PrimeField::<P>::ZERO; N]);

//   fn inverse(&self) -> Option<Self> { todo!() }

//   fn pow(self, power: u32) -> Self { todo!() }
// }

const fn single_instance_array<const N: usize, const P: u32>(
  value: PrimeField<P>,
) -> [PrimeField<P>; N] {
  let mut arr = [PrimeField::<P>::ZERO; N];
  arr[0] = value;
  arr
}

// TODO: We could get the irreducible polynomial with const fn
/// A polynomial is irreducible if `x^(p^q) - x` is divisible by the polynomial.
// const fn get_irreducible_poly<const N: usize, const P: u32>() -> [PrimeField<P>; N + 1]
// where [(); P as usize * N + 1]: {
//   // Make our polynomial x^(p^q) - x
//   let mut divisible = [PrimeField::<P>::ZERO; P as usize * N + 1];
//   divisible[1] = PrimeField::<P>::NEG_ONE;
//   divisible[P as usize * N] = PrimeField::<P>::ONE;
//   let divisible = Polynomial::<Monomial, PrimeField<P>>::from(divisible);

//   let mut poly = Polynomial::<Monomial, PrimeField<P>>::from([PrimeField::<P>::ZERO; N + 1]);

//   for i in 0..N + 1 {
//     for j in 0..P as usize * i {
//       poly.coefficients[j / i] = PrimeField::<P>::new((j % i) as u32);
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

impl<const N: usize, const P: u32> Default for GaloisField<N, P> {
  fn default() -> Self { Self { coeffs: [PrimeField::<P>::ZERO; N] } }
}

impl<const N: usize, const P: u32> GaloisField<N, P> {
  /// Create a new extension field element from the given coefficients of the field in polynomial
  /// form. The coefficients are expected to be from [`FiniteField`] you are extending over in the
  /// order of increasing degree. For example, for a quadratic (`N=2`) extension field, the
  /// coefficients are `[a, b]` where `a + b * t`.
  pub const fn new(coeffs: [PrimeField<P>; N]) -> Self { Self { coeffs } }
}

/// Convert from a [`FiniteField`] element into the [`Ext`] field element in the natural way.
impl<const N: usize, const P: u32> From<PrimeField<P>> for GaloisField<N, P> {
  fn from(value: PrimeField<P>) -> Self {
    let mut coeffs = [PrimeField::<P>::ZERO; N];
    coeffs[0] = value;
    Self { coeffs }
  }
}

/// Convert from a [`u32`] into the [`Ext`] field element in the natural way.
impl<const N: usize, const P: u32> From<u32> for GaloisField<N, P> {
  fn from(val: u32) -> Self { Self::from(PrimeField::<P>::from(val)) }
}

/// Convert from a [`u64`] into the [`Ext`] field element in the natural way.
impl<const N: usize, const P: u32> From<u64> for GaloisField<N, P> {
  fn from(val: u64) -> Self { Self::from(PrimeField::<P>::from(val as u32)) }
}