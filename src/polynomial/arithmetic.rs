// use std::array;

// use super::*;

// // TODO: Implement `Mul`, `MulAssign`, `Product`, `Div`, `DivAssign`, `Neg`, `Rem`.
// // * `Mul` and other products will require FFT.
// // * `Div` and `Rem` will require Euclidean division.

// impl<const N: usize, B: Basis, F: FiniteField> Add for Polynomial<N, B, F> {
//   type Output = Self;

//   fn add(self, rhs: Self) -> Self {
//     let mut coefficients = [F::zero(); N];
//     for i in 0..N {
//       coefficients[i] = self.coefficients[i] + rhs.coefficients[i];
//     }
//     Self { coefficients, basis: self.basis }
//   }
// }

// impl<const N: usize, B: Basis, F: FiniteField> AddAssign for Polynomial<N, B, F> {
//   fn add_assign(&mut self, rhs: Self) {
//     for i in 0..N {
//       self.coefficients[i] += rhs.coefficients[i];
//     }
//   }
// }

// impl<const N: usize, B: Basis, F: FiniteField> Sum for Polynomial<N, B, F> {
//   fn sum<I: Iterator<Item = Self>>(iter: I) -> Self { iter.reduce(|x, y| x + y).unwrap() }
// }

// impl<const N: usize, B: Basis, F: FiniteField> Sub for Polynomial<N, B, F> {
//   type Output = Self;

//   fn sub(self, rhs: Self) -> Self {
//     let mut coefficients = [F::zero(); N];
//     for i in 0..N {
//       coefficients[i] = self.coefficients[i] - rhs.coefficients[i];
//     }
//     Self { coefficients, basis: self.basis }
//   }
// }

// impl<const N: usize, B: Basis, F: FiniteField> SubAssign for Polynomial<N, B, F> {
//   fn sub_assign(&mut self, rhs: Self) {
//     for i in 0..N {
//       self.coefficients[i] -= rhs.coefficients[i];
//     }
//   }
// }

// impl<const N: usize, B: Basis, F: FiniteField> Neg for Polynomial<N, B, F> {
//   type Output = Self;

//   fn neg(self) -> Self {
//     let mut coefficients = [F::zero(); N];
//     for i in 0..N {
//       coefficients[i] = -self.coefficients[i];
//     }
//     Self { coefficients, basis: self.basis }
//   }
// }

// impl<const M: usize, const N: usize, F: FiniteField> Div<Polynomial<N, Monomial, F>>
//   for Polynomial<M, Monomial, F>
// where
//   [(); M - N]:,
//   [(); M + N]:,
// {
//   type Output = Polynomial<{ M - N }, Monomial, F>;

//   fn div(self, rhs: Polynomial<N, Monomial, F>) -> Self::Output {
//     // Euclidean division
//     // Initial quotient value
//     let mut q = F::zero();

//     // Initial remainder value is our numerator polynomial
//     let mut p = self;

//     // Leading coefficient of the denominator
//     let c = rhs.leading_coefficient();

//     #[allow(clippy::suspicious_arithmetic_impl)]
//     let mut q = Polynomial::<{ M - N }, Monomial, F>::new([F::zero(); M - N]);
//     for i in M - N..0 {
//       let s = p.leading_coefficient() * c.inverse().unwrap();
//       q.coefficients[i] = s;
//       p -= rhs.pow_mult::<{ i }>(s);
//     }

//     q
//   }
// }

// impl<const N: usize, F: FiniteField> Rem for Polynomial<N, Monomial, F> {
//   type Output = Self;

//   fn rem(self, _rhs: Self) -> Self { unimplemented!() }
// }

// #[cfg(test)]
// mod tests {
//   use field::gf_101::GF101;

//   use super::*;

//   fn poly_a() -> Polynomial<4, Monomial, GF101> {
//     Polynomial::<4, Monomial, GF101>::new([
//       GF101::new(1),
//       GF101::new(2),
//       GF101::new(3),
//       GF101::new(4),
//     ])
//   }

//   fn poly_b() -> Polynomial<4, Monomial, GF101> {
//     Polynomial::<4, Monomial, GF101>::new([
//       GF101::new(5),
//       GF101::new(6),
//       GF101::new(7),
//       GF101::new(8),
//     ])
//   }

//   #[test]
//   fn add() {
//     let c = poly_a() + poly_b();
//     assert_eq!(c.coefficients, [GF101::new(6), GF101::new(8), GF101::new(10), GF101::new(12)]);

//     let conv_c = poly_a().to_lagrange() + poly_b().to_lagrange();
//     let lagrange_c = c.to_lagrange();

//     for i in 0..4 {
//       assert_eq!(conv_c.coefficients[i], lagrange_c.coefficients[i]);
//     }
//   }

//   #[test]
//   fn add_assign() {
//     let mut a = poly_a();
//     a += poly_b();
//     assert_eq!(a.coefficients, [GF101::new(6), GF101::new(8), GF101::new(10), GF101::new(12)]);
//   }

//   #[test]
//   fn sum() {
//     let sum = [poly_a(), poly_b()].into_iter().sum::<Polynomial<4, Monomial, GF101>>();
//     assert_eq!(sum.coefficients, [GF101::new(6), GF101::new(8), GF101::new(10), GF101::new(12)]);
//   }

//   #[test]
//   fn sub() {
//     let c = poly_a() - poly_b();
//     assert_eq!(c.coefficients, [GF101::new(97), GF101::new(97), GF101::new(97), GF101::new(97)]);
//   }

//   #[test]
//   fn sub_assign() {
//     let mut a = poly_a();
//     a -= poly_b();
//     assert_eq!(a.coefficients, [GF101::new(97), GF101::new(97), GF101::new(97), GF101::new(97)]);
//   }

//   #[test]
//   fn neg() {
//     let a = -poly_a();
//     assert_eq!(a.coefficients, [GF101::new(100), GF101::new(99), GF101::new(98),
// GF101::new(97)]);   }

//   #[test]
//   fn div() { let c = poly_a() / poly_b(); }
// }
