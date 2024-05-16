//! This module contains an implementation of the quadratic extension field GF(101^2).
//! Elements represented as coefficients of a [`Polynomial`] in the [`Monomial`] basis of degree 1
//! in form: `a_0 + a_1*t`` where {a_0, a_1} \in \mathhbb{F}. Uses irreducible poly of the form:
//! (X^2-K).
//!
//! The curve used in [`curves::g1_curve`] supports degree two extension field from GF(101) to have
//! points in GF(101^2). This can be verified by finding out embedding degree of the curve, i.e.
//! smallest k such that r|q^k-1.

use super::*;

impl ExtensionField<2, 101> for PlutoBaseFieldExtension {
  /// irreducible polynomial used to reduce field polynomials to second degree:
  /// F[X]/(X^2-2)
  const IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS: [PlutoBaseField; 3] =
    [PlutoBaseField::new(2), PlutoBaseField::ZERO, PlutoBaseField::ONE];
}

impl FiniteField for PlutoBaseFieldExtension {
  const ONE: Self = Self::new([PlutoBaseField::ONE, PlutoBaseField::ZERO]);
  const ORDER: usize = PlutoExtensions::QuadraticBase as usize;
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
  const PRIMITIVE_ELEMENT: Self = Self::new([PlutoBaseField::new(14), PlutoBaseField::new(9)]);
  const ZERO: Self = Self::new([PlutoBaseField::ZERO, PlutoBaseField::ZERO]);

  /// Computes the multiplicative inverse of `a`, i.e. 1 / (a0 + a1 * t).
  /// Multiply by `a0 - a1 * t` in numerator and denominator.
  /// Denominator equals `(a0 + a1 * t) * (a0 - a1 * t) = a0.pow(2) - a1.pow(2) * Q::residue()`
  fn inverse(&self) -> Option<Self> {
    if *self == Self::ZERO {
      return None;
    }

    let mut res = Self::default();
    let scalar = (self.coeffs[0].pow(2) + PlutoBaseField::from(2u32) * self.coeffs[1].pow(2))
      .inverse()
      .unwrap();
    res.coeffs[0] = self.coeffs[0] * scalar;
    res.coeffs[1] = -self.coeffs[1] * scalar;
    Some(res)
  }

  fn pow(self, power: usize) -> Self {
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
impl Mul for PlutoBaseFieldExtension {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    let poly_self = Polynomial::<Monomial, PlutoBaseField>::from(self);
    let poly_rhs = Polynomial::<Monomial, PlutoBaseField>::from(rhs);
    let poly_irred =
      Polynomial::<Monomial, PlutoBaseField>::from(Self::IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS);
    let product = (poly_self * poly_rhs) % poly_irred;
    let res: [PlutoBaseField; 2] =
      array::from_fn(|i| product.coefficients.get(i).cloned().unwrap_or(PlutoBaseField::ZERO));
    Self::new(res)
  }
}

impl MulAssign for PlutoBaseFieldExtension {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}
impl Product for PlutoBaseFieldExtension {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl Div for PlutoBaseFieldExtension {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().expect("invalid inverse") }
}

impl DivAssign for PlutoBaseFieldExtension {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs }
}

impl Rem for PlutoBaseFieldExtension {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn new() {
    let order = <PlutoBaseFieldExtension>::ORDER;
    assert_eq!(order, PlutoExtensions::QuadraticBase as usize);
  }

  #[test]
  fn from() {
    let x = PlutoBaseField::new(10);
    let x_2 = <PlutoBaseFieldExtension>::from(x);

    assert_eq!(x_2.coeffs[0], PlutoBaseField::new(10));
    assert_eq!(x_2.coeffs[1], PlutoBaseField::new(0));
  }

  #[rstest]
  #[case(
    <PlutoBaseFieldExtension>::new([PlutoBaseField::new(10), PlutoBaseField::new(20)]),
    <PlutoBaseFieldExtension>::new([PlutoBaseField::new(20), PlutoBaseField::new(10)]),
    <PlutoBaseFieldExtension>::new([PlutoBaseField::new(30), PlutoBaseField::new(30)])
  )]
  #[case(
    <PlutoBaseFieldExtension>::new([PlutoBaseField::new(70), PlutoBaseField::new(80)]),
    <PlutoBaseFieldExtension>::new([PlutoBaseField::new(80), PlutoBaseField::new(70)]),
    <PlutoBaseFieldExtension>::new([PlutoBaseField::new(49), PlutoBaseField::new(49)])
  )]

  fn add(
    #[case] a: PlutoBaseFieldExtension,
    #[case] b: PlutoBaseFieldExtension,
    #[case] expected: PlutoBaseFieldExtension,
  ) {
    assert_eq!(a + b, expected);
  }

  #[test]
  fn neg() {
    let a = <PlutoBaseFieldExtension>::new([PlutoBaseField::new(10), PlutoBaseField::new(20)]);
    assert_eq!(
      -a,
      <PlutoBaseFieldExtension>::new([PlutoBaseField::new(91), PlutoBaseField::new(81)])
    );
  }

  #[test]
  fn sub() {
    let a = <PlutoBaseFieldExtension>::new([PlutoBaseField::new(10), PlutoBaseField::new(20)]);
    let b = <PlutoBaseFieldExtension>::new([PlutoBaseField::new(20), PlutoBaseField::new(10)]);
    assert_eq!(
      a - b,
      <PlutoBaseFieldExtension>::new([PlutoBaseField::new(91), PlutoBaseField::new(10)])
    );
  }

  #[test]
  fn mul() {
    let a = <PlutoBaseFieldExtension>::new([PlutoBaseField::new(10), PlutoBaseField::new(20)]);
    let b = <PlutoBaseFieldExtension>::new([PlutoBaseField::new(20), PlutoBaseField::new(10)]);
    assert_eq!(
      a * b,
      <PlutoBaseFieldExtension>::new([PlutoBaseField::new(2), PlutoBaseField::new(96)])
    );
  }

  #[test]
  fn add_sub_neg_mul() {
    let mut rng = rand::thread_rng();
    let x = <PlutoBaseFieldExtension>::from(rng.gen::<PlutoBaseField>());
    let y = <PlutoBaseFieldExtension>::from(rng.gen::<PlutoBaseField>());
    let z = <PlutoBaseFieldExtension>::from(rng.gen::<PlutoBaseField>());
    assert_eq!(x + (-x), <PlutoBaseFieldExtension>::ZERO);
    assert_eq!(-x, <PlutoBaseFieldExtension>::ZERO - x);
    assert_eq!(
      x + x,
      x * <PlutoBaseFieldExtension>::new([PlutoBaseField::new(2), PlutoBaseField::ZERO])
    );
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
    let x = <PlutoBaseFieldExtension>::from(rng.gen::<PlutoBaseField>());

    assert_eq!(x, x.pow(1));

    let res = x.pow(4);
    assert_eq!(res, x * x * x * x);
  }

  #[test]
  fn inv_div() {
    let mut rng = rand::thread_rng();
    // Loop rng's until we get something with inverse.
    let mut x = <PlutoBaseFieldExtension>::ZERO;
    let mut x_inv = None;
    while x_inv.is_none() {
      x = <PlutoBaseFieldExtension>::from(rng.gen::<PlutoBaseField>());
      x_inv = x.inverse();
    }
    let mut y = <PlutoBaseFieldExtension>::ZERO;
    let mut y_inv = None;
    while y_inv.is_none() {
      y = <PlutoBaseFieldExtension>::from(rng.gen::<PlutoBaseField>());
      y_inv = y.inverse();
    }
    let mut z = <PlutoBaseFieldExtension>::ZERO;
    let mut z_inv = None;
    while z_inv.is_none() {
      z = <PlutoBaseFieldExtension>::from(rng.gen::<PlutoBaseField>());
      z_inv = z.inverse();
    }
    assert_eq!(x * x.inverse().unwrap(), <PlutoBaseFieldExtension>::ONE);
    assert_eq!(
      x.inverse().unwrap_or(<PlutoBaseFieldExtension>::ONE) * x,
      <PlutoBaseFieldExtension>::ONE
    );
    assert_eq!(
      (x * x).inverse().unwrap_or(<PlutoBaseFieldExtension>::ONE),
      x.inverse().unwrap_or(<PlutoBaseFieldExtension>::ONE).pow(2)
    );
    assert_eq!((x / y) * y, x);
    assert_eq!(x / (y * z), (x / y) / z);
    assert_eq!((x * y) / z, x * (y / z));
  }

  #[test]
  fn generator() {
    assert_eq!(
      <PlutoBaseFieldExtension>::PRIMITIVE_ELEMENT
        * PrimeField::<{ PlutoPrime::Base as usize }>::ZERO,
      <PlutoBaseFieldExtension>::ZERO
    );
  }

  #[test]
  fn add_sub_mul_subfield() {
    let mut rng = rand::thread_rng();
    let x = <PlutoBaseFieldExtension>::from(rng.gen::<PlutoBaseField>());
    let mut y = <PlutoBaseFieldExtension>::ZERO;
    let mut y_inv = None;
    while y_inv.is_none() {
      y = <PlutoBaseFieldExtension>::from(rng.gen::<PlutoBaseField>());
      y_inv = y.inverse();
    }

    let add1 = x + y;
    let sub1 = x - y;
    let res: PlutoBaseFieldExtension = x * PrimeField::<{ PlutoPrime::Base as usize }>::new(2);
    assert_eq!(add1 + sub1, res);

    let mul1 = x * y;
    let inv_mul = x * y.inverse().unwrap();
    let res = x * x;
    assert_eq!(mul1 * inv_mul, res);
  }

  #[test]
  fn generator_order() {
    let generator = <PlutoBaseFieldExtension>::PRIMITIVE_ELEMENT;

    let mut val = generator;
    for _ in 0..<PlutoBaseFieldExtension>::ORDER - 1 {
      val *= generator;
    }
    assert_eq!(val, generator);
  }
}
