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

impl FieldExt for GaloisField<2, 101> {
  /// Computes euler criterion of the field element, i.e. Returns true if the element is a quadratic
  /// residue (a square number) in the field.
  fn euler_criterion(&self) -> bool { self.norm().euler_criterion() }

  /// Computes square root of the quadratic field element `(x_0 + x_1*u)` (if it exists) and return
  /// a tuple of `(r, -r)` where `r` is lower.
  ///
  /// - `(a_0 + a_1*u)^2 = a_0^2+2*a_0*a_1*u+βa_1^2 = (x_0 + x_1*u)`. Equating x_0 and x_1 with LHS:
  /// - `x_0 = a_0^2 + βa_1^2`
  /// - `x_1 = 2a_0*a_1`
  fn sqrt(&self) -> Option<(Self, Self)> {
    let (a0, a1) = (self.coeffs[0], self.coeffs[1]);

    // irreducible poly: F[X]/(X^2+2)
    let residue = -PlutoBaseFieldExtension::IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS[0];

    // x_0 = a_0^2 + βa_1^2
    if a1 == PlutoBaseField::ZERO {
      // if a_1 = 0, then straight away compute sqrt of a_0 as base field element
      if a0.euler_criterion() {
        return a0.sqrt().map(|(res0, res1)| (Self::from(res0), Self::from(res1)));
      } else {
        // if a_0 is not a square, then compute a_1 = sqrt(x_0 / β)
        return a0.div(residue).sqrt().map(|(res0, res1)| {
          (Self::new([PlutoBaseField::ZERO, res0]), Self::new([PlutoBaseField::ZERO, res1]))
        });
      }
    }

    // x_0 = ((a_0 ± (a_0² − βa_1²)^½)/2)^½
    // x_1 = a_1/(2x_0)

    // α = (a_0² − βa_1²)
    let alpha = self.norm();
    let two_inv = PlutoBaseField::new(2).inverse().expect("2 should have an inverse");

    alpha.sqrt().map(|(alpha, _)| {
      let mut delta = (alpha + a0) * two_inv;
      if !delta.euler_criterion() {
        delta -= alpha;
      }

      let x0 = delta.sqrt().expect("delta must have an square root").0;
      let x0_inv = x0.inverse().expect("x0 must have an inverse");
      let x1 = a1 * two_inv * x0_inv;
      let x = Self::new([x0, x1]);
      if -x < x {
        (-x, x)
      } else {
        (x, -x)
      }
    })
  }
}
///////////////////////////////////////////////////////////////////////////////////////////////
