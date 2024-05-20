//! Arithmetic operations for RSA fields.
use super::*;

impl<const N: usize> From<usize> for RSAField<N> {
  fn from(val: usize) -> Self { Self::new(val) }
}

impl<const N: usize> const Add for RSAField<N> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self { Self { value: (self.value + rhs.value) % Self::ORDER } }
}

impl<const N: usize> AddAssign for RSAField<N> {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<const N: usize> Sum for RSAField<N> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO)
  }
}

impl<const N: usize> Sub for RSAField<N> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let (mut diff, over) = self.value.overflowing_sub(rhs.value);
    let corr = if over { Self::ORDER } else { 0 };
    diff = diff.wrapping_add(corr);
    Self { value: diff }
  }
}

impl<const N: usize> SubAssign for RSAField<N> {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<const N: usize> Mul for RSAField<N> {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self { Self { value: (self.value * rhs.value) % Self::ORDER } }
}

impl<const N: usize> MulAssign for RSAField<N> {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<const N: usize> Product for RSAField<N> {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl<const N: usize> Div for RSAField<N> {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self { self * rhs.inverse().unwrap() }
}

impl<const N: usize> DivAssign for RSAField<N> {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl<const N: usize> Neg for RSAField<N> {
  type Output = Self;

  fn neg(self) -> Self::Output { Self::ZERO - self }
}

impl<const N: usize> Rem for RSAField<N> {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self { self - (self / rhs) * rhs }
}
