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

#[cfg(test)]
mod tests {
  use field::gf_101::GF101;

  use super::*;

  fn poly_a() -> Polynomial<4, Monomial, GF101> {
    Polynomial::<4, Monomial, GF101>::new([
      GF101::new(1),
      GF101::new(2),
      GF101::new(3),
      GF101::new(4),
    ])
  }

  fn poly_b() -> Polynomial<4, Monomial, GF101> {
    Polynomial::<4, Monomial, GF101>::new([
      GF101::new(5),
      GF101::new(6),
      GF101::new(7),
      GF101::new(8),
    ])
  }

  #[test]
  fn add() {
    let c = poly_a() + poly_b();
    assert_eq!(c.coefficients, [GF101::new(6), GF101::new(8), GF101::new(10), GF101::new(12)]);

    let conv_c = poly_a().to_lagrange() + poly_b().to_lagrange();
    let lagrange_c = c.to_lagrange();

    for i in 0..4 {
      assert_eq!(conv_c.coefficients[i], lagrange_c.coefficients[i]);
    }
  }

  #[test]
  fn add_assign() {
    let mut a = poly_a();
    a += poly_b();
    assert_eq!(a.coefficients, [GF101::new(6), GF101::new(8), GF101::new(10), GF101::new(12)]);
  }

  #[test]
  fn sum() {
    let sum = [poly_a(), poly_b()].into_iter().sum::<Polynomial<4, Monomial, GF101>>();
    assert_eq!(sum.coefficients, [GF101::new(6), GF101::new(8), GF101::new(10), GF101::new(12)]);
  }

  #[test]
  fn sub() {
    let c = poly_a() - poly_b();
    assert_eq!(c.coefficients, [GF101::new(97), GF101::new(97), GF101::new(97), GF101::new(97)]);
  }

  #[test]
  fn sub_assign() {
    let mut a = poly_a();
    a -= poly_b();
    assert_eq!(a.coefficients, [GF101::new(97), GF101::new(97), GF101::new(97), GF101::new(97)]);
  }

  #[test]
  fn neg() {
    let a = -poly_a();
    assert_eq!(a.coefficients, [GF101::new(100), GF101::new(99), GF101::new(98), GF101::new(97)]);
  }
}
