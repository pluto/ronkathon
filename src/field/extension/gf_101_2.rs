//! This module contains an implementation of the quadratic extension field GF(101^2).
//! Elements represented as coefficients of a [`Polynomial`] in the [`Monomial`] basis of degree 1
//! in form: `a_0 + a_1*t`` where {a_0, a_1} \in \mathhbb{F}. Uses irreducible poly of the form:
//! (X^2-K).
//!
//! The curve used in [`curves::g1_curve`] supports degree two extension field from GF(101) to have
//! points in GF(101^2). This can be verified by finding out embedding degree of the curve, i.e.
//! smallest k such that r|q^k-1.

use super::*;

const QUADRATIC_EXTENSION_FIELD_ORDER: u32 = 101 * 101;

impl ExtensionField<2, 101> for GaloisField<2, 101> {
  /// irreducible polynomial used to reduce field polynomials to second degree:
  /// F[X]/(X^2-2)
  const IRREDUCIBLE_POLYNOMIAL_COEFFS: [PrimeField<101>; 3] =
    [PrimeField::<101>::TWO, PrimeField::<101>::ZERO, PrimeField::<101>::ONE];
}

impl FiniteField for GaloisField<2, 101> {
  /// Retrieves a multiplicative generator for GF(101) inside of [`Ext<2, GF101>`].
  /// This can be verified using sage script
  /// ```sage
  /// F = GF(101)
  /// Ft.<t> = F[]
  /// P = Ft(t ^ 2 - 2)
  /// F_2 = GF(101 ^ 2, name="t", modulus=P)
  /// f_2_primitive_element = F_2([2, 1])
  /// assert f_2_primitive_element.multiplicative_order() == 101^2-1
  /// ```
  const GENERATOR: Self = Self::new([PrimeField::<101>::new(14), PrimeField::<101>::new(9)]);
  const NEG_ONE: Self = Self::new([PrimeField::<101>::NEG_ONE, PrimeField::<101>::ZERO]);
  const ONE: Self = Self::new([PrimeField::<101>::ONE, PrimeField::<101>::ZERO]);
  const ORDER: u32 = QUADRATIC_EXTENSION_FIELD_ORDER;
  const THREE: Self = Self::new([PrimeField::<101>::THREE, PrimeField::<101>::ZERO]);
  const TWO: Self = Self::new([PrimeField::<101>::TWO, PrimeField::<101>::ZERO]);
  const ZERO: Self = Self::new([PrimeField::<101>::ZERO, PrimeField::<101>::ZERO]);

  /// Computes the multiplicative inverse of `a`, i.e. 1 / (a0 + a1 * t).
  /// Multiply by `a0 - a1 * t` in numerator and denominator.
  /// Denominator equals `(a0 + a1 * t) * (a0 - a1 * t) = a0.pow(2) - a1.pow(2) * Q::residue()`
  fn inverse(&self) -> Option<Self> {
    if *self == Self::ZERO {
      return None;
    }

    let mut res = Self::default();
    let scalar = (self.coeffs[0].pow(2) + PrimeField::<101>::from(2u32) * self.coeffs[1].pow(2))
      .inverse()
      .unwrap();
    res.coeffs[0] = self.coeffs[0] * scalar;
    res.coeffs[1] = -self.coeffs[1] * scalar;
    Some(res)
  }

  fn pow(self, power: u32) -> Self {
    if power == 0 {
      Self::ONE
    } else if power == 1 {
      self
    } else if power % 2 == 0 {
      self.pow(power / 2) * self.pow(power / 2)
    } else {
      self.pow(power / 2) * self.pow(power / 2) * self
    }
  }
}

/// Returns the multiplication of two [`Ext<2, GF101>`] elements by reducing result modulo
/// irreducible polynomial.
impl Mul for GaloisField<2, 101> {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    let poly_self = Polynomial::<Monomial, PrimeField<101>>::from(self);
    let poly_rhs = Polynomial::<Monomial, PrimeField<101>>::from(rhs);
    let poly_irred =
      Polynomial::<Monomial, PrimeField<101>>::from(Self::IRREDUCIBLE_POLYNOMIAL_COEFFS);
    let product = (poly_self * poly_rhs) % poly_irred;
    let res: [PrimeField<101>; 2] =
      array::from_fn(|i| product.coefficients.get(i).cloned().unwrap_or(PrimeField::<101>::ZERO));
    Self::new(res)
  }
}

impl MulAssign for GaloisField<2, 101> {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}
impl Product for GaloisField<2, 101> {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl Div for GaloisField<2, 101> {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().expect("invalid inverse") }
}

impl DivAssign for GaloisField<2, 101> {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs }
}

impl Rem for GaloisField<2, 101> {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn new() {
    let order = <GaloisField<2, 101>>::ORDER;
    assert_eq!(order, 101 * 101);
  }

  #[test]
  fn from() {
    let x = PrimeField::<101>::new(10);
    let x_2 = <GaloisField<2, 101>>::from(x);

    assert_eq!(x_2.coeffs[0], PrimeField::<101>::new(10));
    assert_eq!(x_2.coeffs[1], PrimeField::<101>::new(0));
  }

  #[rstest]
  #[case(
    <GaloisField<2, 101>>::new([PrimeField::<101>::new(10), PrimeField::<101>::new(20)]),
    <GaloisField<2, 101>>::new([PrimeField::<101>::new(20), PrimeField::<101>::new(10)]),
    <GaloisField<2, 101>>::new([PrimeField::<101>::new(30), PrimeField::<101>::new(30)])
  )]
  #[case(
    <GaloisField<2, 101>>::new([PrimeField::<101>::new(70), PrimeField::<101>::new(80)]),
    <GaloisField<2, 101>>::new([PrimeField::<101>::new(80), PrimeField::<101>::new(70)]),
    <GaloisField<2, 101>>::new([PrimeField::<101>::new(49), PrimeField::<101>::new(49)])
  )]

  fn add(
    #[case] a: GaloisField<2, 101>,
    #[case] b: GaloisField<2, 101>,
    #[case] expected: GaloisField<2, 101>,
  ) {
    assert_eq!(a + b, expected);
  }

  #[test]
  fn neg() {
    let a = <GaloisField<2, 101>>::new([PrimeField::<101>::new(10), PrimeField::<101>::new(20)]);
    assert_eq!(
      -a,
      <GaloisField<2, 101>>::new([PrimeField::<101>::new(91), PrimeField::<101>::new(81)])
    );
  }

  #[test]
  fn sub() {
    let a = <GaloisField<2, 101>>::new([PrimeField::<101>::new(10), PrimeField::<101>::new(20)]);
    let b = <GaloisField<2, 101>>::new([PrimeField::<101>::new(20), PrimeField::<101>::new(10)]);
    assert_eq!(
      a - b,
      <GaloisField<2, 101>>::new([PrimeField::<101>::new(91), PrimeField::<101>::new(10)])
    );
  }

  #[test]
  fn mul() {
    let a = <GaloisField<2, 101>>::new([PrimeField::<101>::new(10), PrimeField::<101>::new(20)]);
    let b = <GaloisField<2, 101>>::new([PrimeField::<101>::new(20), PrimeField::<101>::new(10)]);
    assert_eq!(
      a * b,
      <GaloisField<2, 101>>::new([PrimeField::<101>::new(2), PrimeField::<101>::new(96)])
    );
  }

  #[test]
  fn add_sub_neg_mul() {
    let mut rng = rand::thread_rng();
    let x = <GaloisField<2, 101>>::from(rng.gen::<PrimeField<101>>());
    let y = <GaloisField<2, 101>>::from(rng.gen::<PrimeField<101>>());
    let z = <GaloisField<2, 101>>::from(rng.gen::<PrimeField<101>>());
    assert_eq!(x + (-x), <GaloisField<2, 101>>::ZERO);
    assert_eq!(-x, <GaloisField<2, 101>>::ZERO - x);
    assert_eq!(x + x, x * <GaloisField<2, 101>>::TWO);
    assert_eq!(x * (-x), -(x * x));
    assert_eq!(x + y, y + x);
    assert_eq!(x * y, y * x);
    assert_eq!(x * (y * z), (x * y) * z);
    assert_eq!(x - (y + z), (x - y) - z);
    assert_eq!((x + y) - z, x + (y - z));
    assert_eq!(x * (y + z), x * y + x * z);
    assert_eq!(x + y + z + x + y + z, [x, x, y, y, z, z].iter().cloned().sum());
  }

  #[test]
  fn pow() {
    let mut rng = rand::thread_rng();
    let x = <GaloisField<2, 101>>::from(rng.gen::<PrimeField<101>>());

    assert_eq!(x, x.pow(1));

    let res = x.pow(4);
    assert_eq!(res, x * x * x * x);
  }

  #[test]
  fn inv_div() {
    let mut rng = rand::thread_rng();
    // Loop rng's until we get something with inverse.
    let mut x = <GaloisField<2, 101>>::ZERO;
    let mut x_inv = None;
    while x_inv.is_none() {
      x = <GaloisField<2, 101>>::from(rng.gen::<PrimeField<101>>());
      x_inv = x.inverse();
    }
    let mut y = <GaloisField<2, 101>>::ZERO;
    let mut y_inv = None;
    while y_inv.is_none() {
      y = <GaloisField<2, 101>>::from(rng.gen::<PrimeField<101>>());
      y_inv = y.inverse();
    }
    let mut z = <GaloisField<2, 101>>::ZERO;
    let mut z_inv = None;
    while z_inv.is_none() {
      z = <GaloisField<2, 101>>::from(rng.gen::<PrimeField<101>>());
      z_inv = z.inverse();
    }
    assert_eq!(x * x.inverse().unwrap(), <GaloisField<2, 101>>::ONE);
    assert_eq!(x.inverse().unwrap_or(<GaloisField<2, 101>>::ONE) * x, <GaloisField<2, 101>>::ONE);
    assert_eq!(
      (x * x).inverse().unwrap_or(<GaloisField<2, 101>>::ONE),
      x.inverse().unwrap_or(<GaloisField<2, 101>>::ONE).pow(2)
    );
    assert_eq!((x / y) * y, x);
    assert_eq!(x / (y * z), (x / y) / z);
    assert_eq!((x * y) / z, x * (y / z));
  }

  #[test]
  fn generator() {
    assert_eq!(
      <GaloisField<2, 101>>::GENERATOR * PrimeField::<101>::ZERO,
      <GaloisField<2, 101>>::ZERO
    );
  }

  #[test]
  fn add_sub_mul_subfield() {
    let mut rng = rand::thread_rng();
    let x = <GaloisField<2, 101>>::from(rng.gen::<PrimeField<101>>());
    let y = rng.gen::<PrimeField<101>>();

    let add1 = x + y;
    let sub1 = x - y;
    let res: GaloisField<2, 101> = x * PrimeField::<101>::TWO;
    assert_eq!(add1 + sub1, res);

    let mul1 = x * y;
    let inv_mul = x * y.inverse().unwrap();
    let res = x * x;
    assert_eq!(mul1 * inv_mul, res);
  }

  #[test]
  fn generator_order() {
    let generator = <GaloisField<2, 101>>::GENERATOR;

    let mut val = generator;
    for _ in 0..<GaloisField<2, 101>>::ORDER - 1 {
      val *= generator;
    }
    assert_eq!(val, generator);
  }
}
