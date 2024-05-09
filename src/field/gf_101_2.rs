use core::{
  iter::{Product, Sum},
  ops::{Add, AddAssign, Mul, Neg, Sub, SubAssign},
};
use std::ops::{Div, DivAssign, MulAssign, Rem};

use serde::{Deserialize, Serialize};

use super::ExtensionField;
use crate::field::FiniteField;

/// Pluto curve with modulus 101 supports two degree extension field. This can be verified
/// by finding out embedding degree of the curve, i.e. smallest k: r|q^k-1
const EXT_DEGREE: usize = 2;
const QUADRATIC_EXTENSION_FIELD_ORDER: u32 = 101 * 101;

#[derive(Clone, Default, Copy, Eq, PartialEq, Hash, Debug, Serialize, Deserialize)]

/// Quadratic Extension field element represented as polynomial of degree 1 in form:
/// a_0 + a_1*t where {a_0, a_1} \in \mathhbb{F}. Uses irreducible poly of the form:
/// (X^2-K).
pub struct QuadraticPlutoField<F: FiniteField> {
  pub(crate) value: [F; 2],
}

impl<F: FiniteField> QuadraticPlutoField<F> {
  const D: usize = 2;

  /// irreducible polynomial used to reduce field polynomials to second degree:
  /// F[X]/(X^2-2)
  fn irreducible() -> F { F::from_canonical_u32(2) }

  // const fn from_base(b: F) -> Self { Self { value: [b, F::zero()] } }

  pub const fn new(a: F, b: F) -> Self { Self { value: [a, b] } }
}

impl<F: FiniteField> ExtensionField<F> for QuadraticPlutoField<F> {
  const D: usize = EXT_DEGREE;

  fn irreducible() -> F { Self::irreducible() }

  fn from_base(b: F) -> Self { Self { value: [b, F::ZERO] } }
}

impl<F: FiniteField> From<F> for QuadraticPlutoField<F> {
  fn from(value: F) -> Self { Self::from_base(value) }
}

impl<F: FiniteField> FiniteField for QuadraticPlutoField<F> {
  type Storage = u32;

  const NEG_ONE: Self = Self::new(F::NEG_ONE, F::ZERO);
  // TODO: This is wrong
  const ONE: Self = Self::new(F::ONE, F::ZERO);
  const ORDER: Self::Storage = QUADRATIC_EXTENSION_FIELD_ORDER;
  const TWO: Self = Self::new(F::TWO, F::ZERO);
  // fn zero() -> Self { Self { value: [F::zero(); EXT_DEGREE] } }
  const ZERO: Self = Self::new(F::ZERO, F::ZERO);

  // field generator: can be verified using sage script
  // ```sage
  // F = GF(101)
  // Ft.<t> = F[]
  // P = Ft(t ^ 2 - 2)
  // F_2 = GF(101 ^ 2, name="t", modulus=P)
  // f_2_primitive_element = F_2([2, 1])
  // assert f_2_primitive_element.multiplicative_order() == 101^2-1
  // ```
  fn generator() -> Self { Self { value: [F::from_canonical_u32(2), F::from_canonical_u32(1)] } }

  /// Computes the multiplicative inverse of `a`, i.e. 1 / (a0 + a1 * t).
  /// Multiply by `a0 - a1 * t` in numerator and denominator.
  /// Denominator equals `(a0 + a1 * t) * (a0 - a1 * t) = a0.pow(2) - a1.pow(2) * Q::residue()`
  fn inverse(&self) -> Option<Self> {
    if *self == Self::ZERO {
      return None;
    }

    let mut res = Self::default();
    let scalar =
      (self.value[0].square() - Self::irreducible() * self.value[1].square()).inverse().unwrap();
    res.value[0] = self.value[0] * scalar;
    res.value[1] = -self.value[1] * scalar;
    Some(res)
  }

  fn primitive_root_of_unity(n: Self::Storage) -> Self { todo!() }

  fn from_canonical_u32(n: u32) -> Self { Self { value: [F::from_canonical_u32(n), F::ZERO] } }
}

impl<F: FiniteField> Add for QuadraticPlutoField<F> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    let mut res = self.value;
    for (r, rhs_val) in res.iter_mut().zip(rhs.value) {
      *r += rhs_val;
    }

    Self { value: res }
  }
}

impl<F: FiniteField> AddAssign for QuadraticPlutoField<F> {
  fn add_assign(&mut self, rhs: Self) { *self = self.clone() + rhs; }
}

impl<F: FiniteField> Add<F> for QuadraticPlutoField<F> {
  type Output = Self;

  fn add(self, rhs: F) -> Self::Output {
    let mut res = self;
    res.value[0] += rhs;
    res
  }
}

impl<F: FiniteField> AddAssign<F> for QuadraticPlutoField<F> {
  fn add_assign(&mut self, rhs: F) { *self = *self + rhs; }
}

impl<F: FiniteField> Sub for QuadraticPlutoField<F> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let mut res = self.value;
    for (r, rhs_val) in res.iter_mut().zip(rhs.value) {
      *r -= rhs_val;
    }

    Self { value: res }
  }
}

impl<F: FiniteField> SubAssign for QuadraticPlutoField<F> {
  fn sub_assign(&mut self, rhs: Self) { *self = self.clone() - rhs; }
}

impl<F: FiniteField> Sub<F> for QuadraticPlutoField<F> {
  type Output = Self;

  fn sub(self, rhs: F) -> Self::Output {
    let mut res = self;
    res.value[0] -= rhs;
    res
  }
}

impl<F: FiniteField> SubAssign<F> for QuadraticPlutoField<F> {
  fn sub_assign(&mut self, rhs: F) { *self = *self - rhs; }
}

impl<F: FiniteField> Sum for QuadraticPlutoField<F> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO)
  }
}

impl<F: FiniteField> Product for QuadraticPlutoField<F> {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl<F: FiniteField> Mul for QuadraticPlutoField<F> {
  type Output = Self;

  /// Returns the multiplication of `a` and `b` using the following equation:
  /// (a0 + a1 * t) * (b0 + b1 * t) = a0 * b0 + a1 * b1 * irreducible() + (a0 * b1 + a1 * b0) * t
  fn mul(self, rhs: Self) -> Self::Output {
    let a = self.value;
    let b = rhs.value;
    let mut res = Self::default();
    res.value[0] = a[0].clone() * b[0].clone() + a[1].clone() * b[1].clone() * Self::irreducible();
    res.value[1] = a[0].clone() * b[1].clone() + a[1].clone() * b[0].clone();
    res
  }
}

impl<F: FiniteField> MulAssign for QuadraticPlutoField<F> {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<F: FiniteField> Mul<F> for QuadraticPlutoField<F> {
  type Output = Self;

  fn mul(self, rhs: F) -> Self::Output {
    let mut res = self;
    res.value[0] *= rhs;
    res.value[1] *= rhs;
    res
  }
}

impl<F: FiniteField> MulAssign<F> for QuadraticPlutoField<F> {
  fn mul_assign(&mut self, rhs: F) { *self = *self * rhs; }
}

impl<F: FiniteField> Div for QuadraticPlutoField<F> {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self::Output { self * rhs.inverse().expect("invalid inverse") }
}

impl<F: FiniteField> DivAssign for QuadraticPlutoField<F> {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs }
}

impl<F: FiniteField> Neg for QuadraticPlutoField<F> {
  type Output = Self;

  fn neg(self) -> Self::Output { Self::ZERO - self }
}

impl<F: FiniteField> Rem for QuadraticPlutoField<F> {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self::Output { self - (self / rhs) * rhs }
}

#[cfg(test)]
mod tests {

  use super::*;
  use crate::field::gf_101::GF101;
  type F = GF101;
  type F2 = QuadraticPlutoField<GF101>;
  use rand::{thread_rng, Rng};

  #[test]
  fn test_field() {
    let order = F2::ORDER;
    assert_eq!(order, 101 * 101);

    let degree = F2::D;
    assert_eq!(2, degree);
  }

  #[test]
  fn test_from_base() {
    let x = F::new(10);
    let x_2 = F2::from_base(x);

    assert_eq!(x_2.value[0], F::new(10));
    assert_eq!(x_2.value[1], F::new(0));
  }

  #[test]
  fn test_add() {
    let a = F2::new(F::new(10), F::new(20));
    let b = F2::new(F::new(20), F::new(10));
    assert_eq!(a + b, F2::new(F::new(30), F::new(30)));
  }

  #[test]
  fn test_sub() {
    let a = F2::new(F::new(10), F::new(20));
    let b = F2::new(F::new(20), F::new(10));
    assert_eq!(a - b, F2::new(F::new(91), F::new(10)));
  }

  #[test]
  fn test_mul() {
    let a = F2::new(F::new(10), F::new(20));
    let b = F2::new(F::new(20), F::new(10));
    assert_eq!(a * b, F2::new(F::new(95), F::new(96)));
  }

  #[test]
  fn test_add_sub_neg_mul() {
    let mut rng = rand::thread_rng();
    let x = F2::from_base(rng.gen::<F>());
    let y = F2::from_base(rng.gen::<F>());
    let z = F2::from_base(rng.gen::<F>());
    assert_eq!(x + (-x), F2::ZERO);
    assert_eq!(-x, F2::ZERO - x);
    assert_eq!(x + x, x * F2::TWO);
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
  fn test_pow() {
    let mut rng = rand::thread_rng();
    let x = F2::from_base(rng.gen::<F>());

    assert_eq!(x, x.pow(<F2 as FiniteField>::Storage::from(1_u32)));

    let res = x.pow(<F2 as FiniteField>::Storage::from(4_u32));
    assert_eq!(res, x.square().square());
  }

  #[test]
  fn test_inv_div() {
    let mut rng = rand::thread_rng();
    // Loop rng's until we get something with inverse.
    let mut x = F2::ZERO;
    let mut x_inv = None;
    while x_inv.is_none() {
      x = F2::from_base(rng.gen::<F>()); 
      x_inv = x.inverse();
    }
    let mut y = F2::ZERO;
    let mut y_inv = None;
    while y_inv.is_none() {
      y = F2::from_base(rng.gen::<F>()); 
      y_inv = y.inverse();
    }
    let mut z = F2::ZERO;
    let mut z_inv = None;
    while z_inv.is_none() {
      z = F2::from_base(rng.gen::<F>()); 
      z_inv = z.inverse();
    }
    assert_eq!(x * x.inverse().unwrap(), F2::ONE);
    assert_eq!(x.inverse().unwrap_or(F2::ONE) * x, F2::ONE);
    assert_eq!(x.square().inverse().unwrap_or(F2::ONE), x.inverse().unwrap_or(F2::ONE).square());
    assert_eq!((x / y) * y, x);
    assert_eq!(x / (y * z), (x / y) / z);
    assert_eq!((x * y) / z, x * (y / z));
  }

  #[test]
  fn test_generator() {
    assert_eq!(F2::generator() * F::from_canonical_u32(F::ORDER), F2::ZERO);
  }

  #[test]
  fn test_add_sub_mul_subfield() {
    let mut rng = rand::thread_rng();
    let x = F2::from_base(rng.gen::<F>());
    let y = rng.gen::<F>();

    let add1 = x + y;
    let sub1 = x - y;
    let res = x * F::TWO;
    assert_eq!(add1 + sub1, res);

    let mul1 = x * y;
    let inv_mul = x * y.inverse().unwrap();
    let res = x.square();
    assert_eq!(mul1 * inv_mul, res);
  }

  // TODO: THIS TEST IS WRONG AND SHOULD BE REWRITTEN
  #[test]
  fn test_generator_order() {
    let generator = F2::generator();
    let mut x = F2::ONE;
    for _ in 1..F2::ORDER {
      x *= generator;
    }
    assert_eq!(x, F2::ONE);
  }
}
