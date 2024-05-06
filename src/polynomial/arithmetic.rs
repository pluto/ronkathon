use super::*;

// TODO: Implement `Mul`, `MulAssign`, `Product`, `Div`, `DivAssign`, `Neg`, `Rem`.
// * `Mul` and other products will require FFT.
// * `Div` and `Rem` will require Euclidean division.

impl<const N: usize, B: Basis, F: FiniteField> Add for Polynomial<N, B, F> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self {
    let mut coefficients = [F::zero(); N];
    for i in 0..N {
      coefficients[i] = self.coefficients[i] + rhs.coefficients[i];
    }
    Self { coefficients, basis: self.basis }
  }
}

impl<const N: usize, B: Basis, F: FiniteField> AddAssign for Polynomial<N, B, F> {
  fn add_assign(&mut self, rhs: Self) {
    for i in 0..N {
      self.coefficients[i] += rhs.coefficients[i];
    }
  }
}

impl<const N: usize, B: Basis, F: FiniteField> Sum for Polynomial<N, B, F> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self { iter.reduce(|x, y| x + y).unwrap() }
}

impl<const N: usize, B: Basis, F: FiniteField> Sub for Polynomial<N, B, F> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let mut coefficients = [F::zero(); N];
    for i in 0..N {
      coefficients[i] = self.coefficients[i] - rhs.coefficients[i];
    }
    Self { coefficients, basis: self.basis }
  }
}

impl<const N: usize, B: Basis, F: FiniteField> SubAssign for Polynomial<N, B, F> {
  fn sub_assign(&mut self, rhs: Self) {
    for i in 0..N {
      self.coefficients[i] -= rhs.coefficients[i];
    }
  }
}

impl<const N: usize, B: Basis, F: FiniteField> Neg for Polynomial<N, B, F> {
  type Output = Self;

  fn neg(self) -> Self {
    let mut coefficients = [F::zero(); N];
    for i in 0..N {
      coefficients[i] = -self.coefficients[i];
    }
    Self { coefficients, basis: self.basis }
  }
}
