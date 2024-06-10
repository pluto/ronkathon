use super::*;

///////////////////////////////////////////////////////////////////////////////////////////////
/// ## Field operations

/// Addition of two [`GaloisField`] elements.
impl<const N: usize, const P: usize> Add for GaloisField<N, P> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    let mut coeffs = self.coeffs;
    for (r, rhs_val) in coeffs.iter_mut().zip(rhs.coeffs) {
      *r += rhs_val;
    }
    Self { coeffs }
  }
}

/// Addition assignment of two [`GaloisField`] elements.
impl<const N: usize, const P: usize> AddAssign for GaloisField<N, P> {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

/// Sum of a collection of [`GaloisField`] elements.
impl<const N: usize, const P: usize> Sum for GaloisField<N, P> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(PrimeField::<P>::ZERO.into())
  }
}

/// Negation of an [`GaloisField`] element.
impl<const N: usize, const P: usize> Neg for GaloisField<N, P> {
  type Output = Self;

  fn neg(self) -> Self::Output {
    // This implementation avoids recursive calls to `sub()`.
    // Be careful changing this and `sub()`!
    let zero = Self::from(PrimeField::<P>::ZERO);
    Self { coeffs: array::from_fn(|i| zero.coeffs[i] - self.coeffs[i]) }
  }
}

/// Subtraction of two [`GaloisField`] elements.
impl<const N: usize, const P: usize> Sub for GaloisField<N, P> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self { self + (-rhs) }
}

/// Subtraction assignment of two [`GaloisField`] elements.
impl<const N: usize, const P: usize> SubAssign for GaloisField<N, P> {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

// TODO: These should be able to be implemented generically for any `N` and `P`.
// /// Returns the multiplication of two [`GaloisField<2, GF101>`] elements by reducing result
// modulo /// irreducible polynomial.
// impl<const N: usize, const P: u32> Mul for GaloisField<N, P> {
//     type Output = Self;

//     fn mul(self, rhs: Self) -> Self::Output {
//       let poly_self = Polynomial::<Monomial, PrimeField<P>>::from(self);
//       let poly_rhs = Polynomial::<Monomial, PrimeField<P>>::from(rhs);
//       let poly_irred =
//         Polynomial::<Monomial, PrimeField<P>>::from(Self::IRREDUCIBLE_POLYNOMIAL_COEFFS);
//       let product = (poly_self * poly_rhs) % poly_irred;
//       let res: [PrimeField<P>; N] =
//         array::from_fn(|i|
// product.coefficients.get(i).cloned().unwrap_or(PrimeField::<P>::ZERO));       Self::new(res)
//     }
//   }

//   impl<const N: usize, const P: u32> MulAssign for GaloisField<N, P> {
//     fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
//   }
//   impl<const N: usize, const P: u32> Product for GaloisField<N, P> {
//     fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
//       iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
//     }
//   }

//   impl<const N: usize, const P: u32> Div for GaloisField<N, P> {
//     type Output = Self;

//     #[allow(clippy::suspicious_arithmetic_impl)]
//     fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().expect("invalid inverse") }
//   }

//   impl<const N: usize, const P: u32> DivAssign for GaloisField<N, P> {
//     fn div_assign(&mut self, rhs: Self) { *self = *self / rhs }
//   }

//   impl<const N: usize, const P: u32> Rem for GaloisField<N, P> {
//     type Output = Self;

//     fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
//   }

///////////////////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////////////////////
/// ## Inclusion of [`FiniteField`] operations

/// Addition of a [`FiniteField`] element to an [`GaloisField`] element.
impl<const N: usize, const P: usize> Add<PrimeField<P>> for GaloisField<N, P> {
  type Output = Self;

  fn add(mut self, rhs: PrimeField<P>) -> Self::Output {
    self.coeffs[0] += rhs;
    self
  }
}

/// Addition assignment of a [`FiniteField`] element to an [`GaloisField`] element.
impl<const N: usize, const P: usize> AddAssign<PrimeField<P>> for GaloisField<N, P> {
  fn add_assign(&mut self, rhs: PrimeField<P>) { *self = *self + rhs; }
}

/// Subtraction of a [`FiniteField`] element from an [`GaloisField`] element.
impl<const N: usize, const P: usize> Sub<PrimeField<P>> for GaloisField<N, P> {
  type Output = Self;

  fn sub(mut self, rhs: PrimeField<P>) -> Self::Output {
    self.coeffs[0] -= rhs;
    self
  }
}

/// Subtraction assignment of a [`FiniteField`] element from an [`GaloisField`] element.
impl<const N: usize, const P: usize> SubAssign<PrimeField<P>> for GaloisField<N, P> {
  fn sub_assign(&mut self, rhs: PrimeField<P>) { *self = *self - rhs; }
}

/// Multiplication of an [`GaloisField`] element by a [`FiniteField`] element.
impl<const N: usize, const P: usize> Mul<PrimeField<P>> for GaloisField<N, P> {
  type Output = Self;

  fn mul(mut self, rhs: PrimeField<P>) -> Self::Output {
    self.coeffs.iter_mut().for_each(|c| *c *= rhs);
    self
  }
}

/// Multiplication assignment of an [`GaloisField`] element by a [`FiniteField`] element.
impl<const N: usize, const P: usize> MulAssign<PrimeField<P>> for GaloisField<N, P> {
  fn mul_assign(&mut self, rhs: PrimeField<P>) { *self = *self * rhs; }
}

impl<const N: usize, const P: usize> Mul<GaloisField<N, P>> for PrimeField<P> {
  type Output = GaloisField<N, P>;

  fn mul(self, rhs: GaloisField<N, P>) -> Self::Output {
    let mut res = rhs;
    res *= self;
    res
  }
}
///////////////////////////////////////////////////////////////////////////////////////////////
