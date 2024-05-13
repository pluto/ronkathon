use super::*;
/// A field extension is a field that contains the original field and additional elements that are
/// not in the original field. The extension field is constructed by adjoining the roots of a
/// polynomial to the original field.
#[const_trait]
pub trait ExtensionField<const N: usize, B: FiniteField>:
  FiniteField
  + From<B>
  + Add<B, Output = Self>
  + AddAssign<B>
  + Sub<B, Output = Self>
  + SubAssign<B>
  + Mul<B, Output = Self>
  + MulAssign<B>
where [B; N + 1]: {
  /// The coefficients of the irreducible polynomial used to reduce field polynomials to the
  /// desired degree.
  const IRREDUCIBLE_POLYNOMIAL_COEFFS: [B; N + 1];
}

/// A struct that represents an element of an extension field. The element is represented as
/// [`Monomial`] coefficients of a [`Polynomial`] of degree `N - 1` over the base [`FiniteField`]
/// `F`.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
pub struct Ext<const N: usize, F: FiniteField> {
  pub(crate) coeffs: [F; N],
}

impl<const N: usize, F: FiniteField> Default for Ext<N, F> {
  fn default() -> Self { Self { coeffs: [F::ZERO; N] } }
}

impl<const N: usize, F: FiniteField> Ext<N, F> {
  /// Create a new extension field element from the given coefficients of the field in polynomial
  /// form. The coefficients are expected to be from [`FiniteField`] you are extending over in the
  /// order of increasing degree. For example, for a quadratic (`N=2`) extension field, the
  /// coefficients are `[a, b]` where `a + b * t`.
  pub const fn new(coeffs: [F; N]) -> Self { Self { coeffs } }
}

/// Convert from a [`FiniteField`] element into the [`Ext`] field element in the natural way.
impl<const N: usize, F: FiniteField> From<F> for Ext<N, F> {
  fn from(value: F) -> Self {
    let mut coeffs = [F::ZERO; N];
    coeffs[0] = value;
    Self { coeffs }
  }
}

/// Convert from a [`u32`] into the [`Ext`] field element in the natural way.
impl<const N: usize, F: FiniteField> From<u32> for Ext<N, F> {
  fn from(val: u32) -> Self { Self::from(F::from(val)) }
}

/// Convert from a [`u64`] into the [`Ext`] field element in the natural way.
impl<const N: usize, F: FiniteField> From<u64> for Ext<N, F> {
  fn from(val: u64) -> Self { Self::from(F::from(val as u32)) }
}

/////////////////////////////////////////////////////////////////////////////////////////////////
/// # Algebraic implementations for N-degree extension fields.
/////////////////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////////////////////////
/// ## Field operations

/// Addition of two [`Ext`] elements.
impl<const N: usize, F: FiniteField> Add for Ext<N, F> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    let mut coeffs = self.coeffs;
    for (r, rhs_val) in coeffs.iter_mut().zip(rhs.coeffs) {
      *r += rhs_val;
    }
    Self { coeffs }
  }
}

/// Addition assignment of two [`Ext`] elements.
impl<const N: usize, F: FiniteField> AddAssign for Ext<N, F> {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

/// Sum of a collection of [`Ext`] elements.
impl<const N: usize, F: FiniteField> Sum for Ext<N, F> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(F::ZERO.into())
  }
}

/// Negation of an [`Ext`] element.
impl<const N: usize, F: FiniteField> Neg for Ext<N, F> {
  type Output = Self;

  fn neg(self) -> Self::Output {
    // This implementation avoids recursive calls to `sub()`.
    // Be careful changing this and `sub()`!
    let zero = Self::from(F::ZERO);
    Self { coeffs: array::from_fn(|i| zero.coeffs[i] - self.coeffs[i]) }
  }
}

/// Subtraction of two [`Ext`] elements.
impl<const N: usize, F: FiniteField> Sub for Ext<N, F> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self { self + (-rhs) }
}

/// Subtraction assignment of two [`Ext`] elements.
impl<const N: usize, F: FiniteField> SubAssign for Ext<N, F> {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

/////////////////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////////////////////////
/// ## Inclusion of [`FiniteField`] operations

/// Addition of a [`FiniteField`] element to an [`Ext`] element.
impl<const N: usize, F: FiniteField> Add<F> for Ext<N, F> {
  type Output = Self;

  fn add(mut self, rhs: F) -> Self::Output {
    self.coeffs[0] += rhs;
    self
  }
}

/// Addition assignment of a [`FiniteField`] element to an [`Ext`] element.
impl<const N: usize, F: FiniteField> AddAssign<F> for Ext<N, F> {
  fn add_assign(&mut self, rhs: F) { *self = *self + rhs; }
}

/// Subtraction of a [`FiniteField`] element from an [`Ext`] element.
impl<const N: usize, F: FiniteField> Sub<F> for Ext<N, F> {
  type Output = Self;

  fn sub(mut self, rhs: F) -> Self::Output {
    self.coeffs[0] -= rhs;
    self
  }
}

/// Subtraction assignment of a [`FiniteField`] element from an [`Ext`] element.
impl<const N: usize, F: FiniteField> SubAssign<F> for Ext<N, F> {
  fn sub_assign(&mut self, rhs: F) { *self = *self - rhs; }
}

/// Multiplication of an [`Ext`] element by a [`FiniteField`] element.
impl<const N: usize, F: FiniteField> Mul<F> for Ext<N, F> {
  type Output = Self;

  fn mul(mut self, rhs: F) -> Self::Output {
    self.coeffs.iter_mut().for_each(|c| *c *= rhs);
    self
  }
}

/// Multiplication assignment of an [`Ext`] element by a [`FiniteField`] element.
impl<const N: usize, F: FiniteField> MulAssign<F> for Ext<N, F> {
  fn mul_assign(&mut self, rhs: F) { *self = *self * rhs; }
}
