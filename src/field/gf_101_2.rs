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

impl ExtensionField<2, GF101> for Ext<2, GF101> {
  /// irreducible polynomial used to reduce field polynomials to second degree:
  /// F[X]/(X^2-2)
  const IRREDUCIBLE_POLYNOMIAL_COEFFS: [GF101; 3] = [GF101::TWO, GF101::ZERO, GF101::ONE];
}

impl FiniteField for Ext<2, GF101> {
  type Storage = u32;

  const NEG_ONE: Self = Self::new([GF101::NEG_ONE, GF101::ZERO]);
  const ONE: Self = Self::new([GF101::ONE, GF101::ZERO]);
  const ORDER: Self::Storage = QUADRATIC_EXTENSION_FIELD_ORDER;
  const THREE: Self = Self::new([GF101::THREE, GF101::ZERO]);
  const TWO: Self = Self::new([GF101::TWO, GF101::ZERO]);
  const ZERO: Self = Self::new([GF101::ZERO, GF101::ZERO]);

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
  fn generator() -> Self { Self { coeffs: [GF101::from(14u32), GF101::from(9u32)] } }

  /// Computes the multiplicative inverse of `a`, i.e. 1 / (a0 + a1 * t).
  /// Multiply by `a0 - a1 * t` in numerator and denominator.
  /// Denominator equals `(a0 + a1 * t) * (a0 - a1 * t) = a0.pow(2) - a1.pow(2) * Q::residue()`
  fn inverse(&self) -> Option<Self> {
    if *self == Self::ZERO {
      return None;
    }

    let mut res = Self::default();
    let scalar =
      (self.coeffs[0].pow(2) + GF101::from(2u32) * self.coeffs[1].pow(2)).inverse().unwrap();
    res.coeffs[0] = self.coeffs[0] * scalar;
    res.coeffs[1] = -self.coeffs[1] * scalar;
    Some(res)
  }
}

/// Returns the multiplication of two [`Ext<2, GF101>`] elements by reducing result modulo
/// irreducible polynomial.
impl Mul for Ext<2, GF101> {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    let poly_self = Polynomial::<Monomial, GF101>::from(self);
    let poly_rhs = Polynomial::<Monomial, GF101>::from(rhs);
    let poly_irred = Polynomial::<Monomial, GF101>::from(Self::IRREDUCIBLE_POLYNOMIAL_COEFFS);
    let product = (poly_self * poly_rhs) % poly_irred;
    let res: [GF101; 2] =
      array::from_fn(|i| product.coefficients.get(i).cloned().unwrap_or(GF101::ZERO));
    Self::new(res)
  }
}

impl MulAssign for Ext<2, GF101> {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}
impl Product for Ext<2, GF101> {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl Div for Ext<2, GF101> {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().expect("invalid inverse") }
}

impl DivAssign for Ext<2, GF101> {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs }
}

impl Rem for Ext<2, GF101> {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn new() {
    let order = <Ext<2, GF101>>::ORDER;
    assert_eq!(order, 101 * 101);

    // let degree = <Ext<2, GF101>>::D;
    // assert_eq!(2, degree);
  }

  #[test]
  fn from() {
    let x = GF101::new(10);
    let x_2 = <Ext<2, GF101>>::from(x);

    assert_eq!(x_2.coeffs[0], GF101::new(10));
    assert_eq!(x_2.coeffs[1], GF101::new(0));
  }

  // TODO: Rewrite this using RSTEST?
  #[test]
  fn add() {
    let a = <Ext<2, GF101>>::new([GF101::new(10), GF101::new(20)]);
    let b = <Ext<2, GF101>>::new([GF101::new(20), GF101::new(10)]);
    assert_eq!(a + b, <Ext<2, GF101>>::new([GF101::new(30), GF101::new(30)]));

    let c = <Ext<2, GF101>>::new([GF101::new(70), GF101::new(80)]);
    let d = <Ext<2, GF101>>::new([GF101::new(80), GF101::new(70)]);
    assert_eq!(c + d, <Ext<2, GF101>>::new([GF101::new(49), GF101::new(49)]));
  }

  #[test]
  fn neg() {
    let a = <Ext<2, GF101>>::new([GF101::new(10), GF101::new(20)]);
    assert_eq!(-a, <Ext<2, GF101>>::new([GF101::new(91), GF101::new(81)]));
  }

  #[test]
  fn sub() {
    let a = <Ext<2, GF101>>::new([GF101::new(10), GF101::new(20)]);
    let b = <Ext<2, GF101>>::new([GF101::new(20), GF101::new(10)]);
    assert_eq!(a - b, <Ext<2, GF101>>::new([GF101::new(91), GF101::new(10)]));
  }

  #[test]
  fn mul() {
    let a = <Ext<2, GF101>>::new([GF101::new(10), GF101::new(20)]);
    let b = <Ext<2, GF101>>::new([GF101::new(20), GF101::new(10)]);
    assert_eq!(a * b, <Ext<2, GF101>>::new([GF101::new(2), GF101::new(96)]));
  }

  #[test]
  fn add_sub_neg_mul() {
    let mut rng = rand::thread_rng();
    let x = <Ext<2, GF101>>::from(rng.gen::<GF101>());
    let y = <Ext<2, GF101>>::from(rng.gen::<GF101>());
    let z = <Ext<2, GF101>>::from(rng.gen::<GF101>());
    assert_eq!(x + (-x), <Ext<2, GF101>>::ZERO);
    assert_eq!(-x, <Ext<2, GF101>>::ZERO - x);
    assert_eq!(x + x, x * <Ext<2, GF101>>::TWO);
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
    let x = <Ext<2, GF101>>::from(rng.gen::<GF101>());

    assert_eq!(x, x.pow(1));

    let res = x.pow(4);
    assert_eq!(res, x * x * x * x);
  }

  #[test]
  fn inv_div() {
    let mut rng = rand::thread_rng();
    // Loop rng's until we get something with inverse.
    let mut x = <Ext<2, GF101>>::ZERO;
    let mut x_inv = None;
    while x_inv.is_none() {
      x = <Ext<2, GF101>>::from(rng.gen::<GF101>());
      x_inv = x.inverse();
    }
    let mut y = <Ext<2, GF101>>::ZERO;
    let mut y_inv = None;
    while y_inv.is_none() {
      y = <Ext<2, GF101>>::from(rng.gen::<GF101>());
      y_inv = y.inverse();
    }
    let mut z = <Ext<2, GF101>>::ZERO;
    let mut z_inv = None;
    while z_inv.is_none() {
      z = <Ext<2, GF101>>::from(rng.gen::<GF101>());
      z_inv = z.inverse();
    }
    assert_eq!(x * x.inverse().unwrap(), <Ext<2, GF101>>::ONE);
    assert_eq!(x.inverse().unwrap_or(<Ext<2, GF101>>::ONE) * x, <Ext<2, GF101>>::ONE);
    assert_eq!(
      (x * x).inverse().unwrap_or(<Ext<2, GF101>>::ONE),
      x.inverse().unwrap_or(<Ext<2, GF101>>::ONE).pow(2)
    );
    assert_eq!((x / y) * y, x);
    assert_eq!(x / (y * z), (x / y) / z);
    assert_eq!((x * y) / z, x * (y / z));
  }

  #[test]
  fn generator() {
    assert_eq!(<Ext<2, GF101>>::generator() * GF101::from(GF101::ORDER), <Ext<2, GF101>>::ZERO);
  }

  #[test]
  fn add_sub_mul_subfield() {
    let mut rng = rand::thread_rng();
    let x = <Ext<2, GF101>>::from(rng.gen::<GF101>());
    let y = rng.gen::<GF101>();

    let add1 = x + y;
    let sub1 = x - y;
    let res = x * GF101::TWO;
    assert_eq!(add1 + sub1, res);

    let mul1 = x * y;
    let inv_mul = x * y.inverse().unwrap();
    let res = x * x;
    assert_eq!(mul1 * inv_mul, res);
  }

  #[test]
  fn generator_order() {
    let generator = <Ext<2, GF101>>::generator();

    let mut val = generator;
    for _ in 0..<Ext<2, GF101>>::ORDER - 1 {
      val *= generator;
    }
    assert_eq!(val, generator);
  }
}
