//! Contains code related the Ed25519 curve and field as given in [RFC8032]
//!
//! References (with abbreviation used in the code)
//! [RFC8032] "Edwards-Curve Digital Signature Algorithm (EdDSA)"
//! [EdwardsRevisited] "Twisted Edwards Curves Revisited", Hisil, H., Wong, K., Carter, G., and E. Dawson
use std::ops::{Add, AddAssign, Mul};

use crypto_bigint::{
  impl_modulus,
  modular::{ConstMontyForm, ConstMontyParams},
  Encoding, U256, U512,
};

// The prime number defining the base field
impl_modulus!(P, U256, "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed");

/// The prime `P` minus 2. This is used for calculation of the inverse.
pub const P_2: U256 =
  U256::from_be_hex("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb");

/// The order of subgroup.
pub const ORDER: U256 =
  U256::from_be_hex("1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed");

// The modulus used by `ScalarField64`
impl_modulus!(
    L64,
    U512,
    "0000000000000000000000000000000000000000000000000000000000000000\
    1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"
);

// The modulus used by 'ScalarField'
impl_modulus!(L, U256, "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed");

/// Type of a 256-bit element of Ed25519 curve's base field
pub type BaseField = ConstMontyForm<P, { U256::LIMBS }>;
/// Type of a 512-bit element of Ed25519 curve's scalar field
pub type ScalarField64 = ConstMontyForm<L64, { U512::LIMBS }>;
/// Type of a 256-bit element of Ed25519 curve's scalar field
pub type ScalarField = ConstMontyForm<L, { U256::LIMBS }>;

/// '0' of type `BaseField`
pub const BF_ZERO: BaseField = BaseField::new(&U256::ZERO);
/// '1' of type `BaseField`
pub const BF_ONE: BaseField = BaseField::new(&U256::ONE);
/// '2' of type `BaseField`
pub const BF_TWO: BaseField = ConstMontyForm::add(&BF_ONE, &BF_ONE);

const D: BaseField = BaseField::new(&U256::from_be_hex(
  "52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3",
));

/// '0' of type `ScalarField`
pub const SF_ZERO: ScalarField = ScalarField::new(&U256::ZERO);
/// '0' of type `ScalarField64`
pub const SF_ZERO64: ScalarField64 = ScalarField64::new(&U512::ZERO);
/// '1' of type `ScalarField`
pub const SF_ONE: ScalarField = ScalarField::new(&U256::ONE);

/// Represents a point on the Ed25519 curve in extended homogenous coordinates.
#[derive(Debug, Clone, Copy)]
pub struct Coordinate {
  x: BaseField,
  y: BaseField,
  t: BaseField,
  z: BaseField,
}

/// The additive identity of the Ed25519 curve group.
pub const IDENTITY: Coordinate = Coordinate::new(BF_ZERO, BF_ONE);
/// The point on the Ed25519 curve used as a generator or base point.
pub const GENERATOR: Coordinate = Coordinate::new(
  BaseField::new(&U256::from_be_hex(
    "216936d3cd6e53fec0a4e231fdd6dc5c692cc7609525a7b2c9562d608f25d51a",
  )),
  BaseField::new(&U256::from_be_hex(
    "6666666666666666666666666666666666666666666666666666666666666658",
  )),
);

#[inline]
fn get_sign_bit(x: &BaseField) -> u8 { x.retrieve().to_le_bytes()[0] & 1 }
#[inline]
fn inv(x: BaseField) -> BaseField { x.pow(&P_2) }

/// Find the square root of an element of the `BaseField`
/// It uses the algorithm given in Section 5.1.1 of [RFC8032] utilizing the special case of
/// `P = 5 (mod 8)`. To read more, see: (https://en.wikipedia.org/wiki/Quadratic_residue#Prime_or_prime_power_modulus)
pub fn sqrt(val: &BaseField) -> Option<BaseField> {
  const TWO: U256 = U256::from_u8(2u8);
  const THREE: U256 = U256::from_u8(3u8);

  let mut exp = (P::MODULUS.get() + THREE).shr(3);
  let y = val.pow(&exp);

  if y * y == *val {
    return Some(y);
  }

  exp = (P::MODULUS.get() - U256::ONE).shr(2);
  let z = BaseField::new(&TWO).pow(&exp);
  let x = y * z;
  if x * x == *val {
    return Some(x);
  } else {
    return None;
  }

}

impl Coordinate {
  /// Create an instance of the `Coordinate` given the affine coordinates of a point on the Ed25519
  /// curve.
  pub const fn new(x: BaseField, y: BaseField) -> Self {
    let z = BF_ONE;
    let t = ConstMontyForm::mul(&x, &y);
    Self { x, y, t, z }
  }

  /// Double the `Coordinate` using the equations for the extended homogenous coordinates which
  /// avoid the expensive field inversion operations given in the section 3.3 of [EdwardsRevisited]
  pub fn double(&self) -> Self {
    let a = self.x.square();
    let b = self.y.square();
    let c = BF_TWO * self.z.square();

    let h = a + b;
    let e = h - (self.x + self.y).square();
    let g = a - b;
    let f = c + g;

    let x = e * f;
    let y = g * h;
    let t = e * h;
    let z = f * g;

    Self { x, y, t, z }
  }

  /// Encode a `Coordinate` on the curve for a compact represetation.
  pub fn encode(&self) -> [u8; 32] {
    let x = self.x * inv(self.z);
    let y = self.y * inv(self.z);
    let mut s = y.retrieve().to_le_bytes();
    if get_sign_bit(&x) == 1u8 {
      s[31] |= 1 << 7;
    }
    s
  }

  /// Decode a `Coordinate` on the curve which is encoded using the `encode` method.
  pub fn decode(mut bytes: [u8; 32]) -> Option<Self> {
    let xsign = bytes[31] >> 7;
    bytes[31] &= !(1 << 7);
    let raw_y = U256::from_le_bytes(bytes);

    if raw_y >= P::MODULUS.get() {
      return None;
    }

    let y = BaseField::new(&raw_y);
    let y2 = y * y;
    let x2 = (y2 - BF_ONE) * inv(D * y2 + BF_ONE);

    let mut x = match sqrt(&x2) {
      Some(x) => x,
      None => return None,
    };

    if x == BF_ZERO && get_sign_bit(&x) != xsign {
      return None;
    }

    if get_sign_bit(&x) != xsign {
      x = -x;
    }

    Some(Coordinate::new(x, y))
  }
}

impl PartialEq for Coordinate {
  fn eq(&self, other: &Self) -> bool {
    // Convert the extended homogenous coordinates to affine coordinates before comparison.
    let x1 = self.x * inv(self.z);
    let y1 = self.y * inv(self.z);

    let x2 = other.x * inv(other.z);
    let y2 = other.y * inv(other.z);

    (x1 == x2) && (y1 == y2)
  }
}

impl Add for Coordinate {
  type Output = Self;

  /// Add two `Coordinate`s, using the equations for the extended homogenous coordinates which
  /// avoid the expensive field inversion operation given the section 3.2 of [EdwardsRevisited]
  fn add(self, rhs: Self) -> Self::Output {
    let a = (self.y - self.x) * (rhs.y - rhs.x);
    let b = (self.y + self.x) * (rhs.y + rhs.x);
    let c = BF_TWO * D * self.t * rhs.t;
    let d = BF_TWO * self.z * rhs.z;
    let e = b - a;
    let f = d - c;
    let g = d + c;
    let h = b + a;

    let x = e * f;
    let y = g * h;
    let t = e * h;
    let z = f * g;

    Self { x, y, t, z }
  }
}

impl AddAssign for Coordinate {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl Mul<ScalarField> for Coordinate {
  type Output = Self;

  /// Multiply a `Coordinate` with a `ScalarField`.
  fn mul(self, rhs: ScalarField) -> Self::Output {
    if rhs == SF_ZERO {
      return IDENTITY;
    }
    let mut t = rhs.retrieve();
    let mut acc = IDENTITY;
    let mut factor = self;
    while t != U256::ZERO {
      if (t & U256::ONE) == U256::ONE {
        acc += factor;
      }
      factor = factor.double();
      t = t.shr(1);
    }
    acc
  }
}
