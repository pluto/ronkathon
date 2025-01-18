//! Contains code related the Ed25519 curve and field as given in [RFC8032]
//!
//! References (with abbreviation used in the code)
//!     1. [RFC8032] "Edwards-Curve Digital Signature Algorithm (EdDSA)"
//!     2. [EdwardsRevisited] "Twisted Edwards Curves Revisited", Hisil, H., Wong, K., Carter, G.,
//!       and E. Dawson
use std::ops::{Add, AddAssign, Mul};

use crypto_bigint::{
  impl_modulus,
  modular::{ConstMontyForm, ConstMontyParams},
  Encoding, U256, U512,
};

// `P`: Prime number defining the base field
impl_modulus!(P, U256, "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed");

/// `P` minus 2. Used for calculation of the inverse.
pub const P_2: U256 =
  U256::from_be_hex("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb");

/// Subgroup order for the Ed25519 curve.
pub const ORDER: U256 =
  U256::from_be_hex("1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed");

// Modulus used by `ScalarField64`
impl_modulus!(
    L64,
    U512,
    "0000000000000000000000000000000000000000000000000000000000000000\
    1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"
);

// Modulus used by 'ScalarField'
impl_modulus!(L, U256, "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed");

/// Type representing a 256-bit element in the Ed25519 curve's base field.
pub type BaseField = ConstMontyForm<P, { U256::LIMBS }>;
/// Type representing a 512-bit element in the Ed25519's scalar field.
pub type ScalarField64 = ConstMontyForm<L64, { U512::LIMBS }>;
/// Type representing a 256-bit element in the Ed25519 curve's scalar field.
pub type ScalarField = ConstMontyForm<L, { U256::LIMBS }>;

/// Constant representing zero in the base field.
pub const BF_ZERO: BaseField = BaseField::new(&U256::ZERO);
/// Constant representing one in the base field.
pub const BF_ONE: BaseField = BaseField::new(&U256::ONE);
/// Constant representing one in the base field.
pub const BF_TWO: BaseField = BaseField::new(&U256::from_u8(2u8));

/// Constant 'd' used in curve operations (refer to [RFC8032] for details).
const D: BaseField = BaseField::new(&U256::from_be_hex(
  "52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3",
));

/// Constant representing zero in the `ScalarField` type.
pub const SF_ZERO: ScalarField = ScalarField::new(&U256::ZERO);
/// Constant representing zero in the `ScalarField64` type.
pub const SF_ZERO64: ScalarField64 = ScalarField64::new(&U512::ZERO);
/// Constant representing one in the `ScalarField` type.
pub const SF_ONE: ScalarField = ScalarField::new(&U256::ONE);

/// Represents a point on the Ed25519 curve in extended homogeneous coordinates.
#[derive(Debug, Clone, Copy)]
pub struct Coordinate {
  x: BaseField,
  y: BaseField,
  t: BaseField,
  z: BaseField,
}

/// The additive identity of the Ed25519 curve group.
pub const IDENTITY: Coordinate = Coordinate::new(BF_ZERO, BF_ONE);

/// The point on the Ed25519 curve used as a generator or base point as defined in [RFC8032]
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

/// Inverse of a element in the BaseField.
/// Calculated as: x^(-1) = x^(P-2) (mod P), where P is modulus of the field.
#[inline]
fn inv(x: BaseField) -> BaseField { x.pow(&P_2) }

/// Find the square root of an element of the `BaseField`
/// It uses the algorithm given in Section 5.1.1 of [RFC8032] utilizing the special case of
/// `P = 5 (mod 8)`. To read more, see: (https://en.wikipedia.org/wiki/Quadratic_residue#Prime_or_prime_power_modulus)
pub fn sqrt(x: &BaseField) -> Option<BaseField> {
  const TWO: U256 = U256::from_u8(2u8);
  const THREE: U256 = U256::from_u8(3u8);

  let mut exp = (P::MODULUS.get() + THREE).shr(3);
  let y1 = x.pow(&exp);

  if y1 * y1 == *x {
    return Some(y1);
  }

  exp = (P::MODULUS.get() - U256::ONE).shr(2);
  let z = BaseField::new(&TWO).pow(&exp);
  let y2 = y1 * z;
  if y2 * y2 == *x {
    Some(y2)
  } else {
    None
  }
}

impl Coordinate {
  /// Creates a new `Coordinate` point on the Ed25519 curve from its affine coordinates (x, y).

  /// **Note:** This constructor assumes the provided `x` and `y` coordinates represent a valid
  /// point on the Ed25519 curve.
  pub const fn new(x: BaseField, y: BaseField) -> Self {
    let z = BF_ONE;
    let t = ConstMontyForm::mul(&x, &y);
    Self { x, y, t, z }
  }

  /// Doubles the current `Coordinate` point.
  ///
  /// This method uses the efficient extended homogeneous coordinates doubling formula from
  /// Section 3.3 of [EdwardsRevisited] to avoid expensive field inversion.
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

  /// Encodes the `Coordinate` point into a compact 32-byte representation.
  ///
  /// This encoding scheme represents the y-coordinate directly and encodes the x-coordinate's
  /// sign in the highest bit of the last byte.
  pub fn encode(&self) -> [u8; 32] {
    let x = self.x * inv(self.z);
    let y = self.y * inv(self.z);

    let mut s = y.retrieve().to_le_bytes();

    // Set the highest bit the y to the sign of x.
    s[31] |= get_sign_bit(&x) << 7;
    s
  }

  /// Decodes a `Coordinate` point from its compact 32-byte representation.
  ///
  /// Returns `None` if the decoding process fails.
  pub fn decode(mut bytes: [u8; 32]) -> Option<Self> {
    let xsign = bytes[31] >> 7;
    bytes[31] &= !(1 << 7);
    let raw_y = U256::from_le_bytes(bytes);

    // Check if raw_y is valid.
    if raw_y >= P::MODULUS.get() {
      return None;
    }

    let y = BaseField::new(&raw_y);
    // Find x^2, given the value of y on the curve.
    let y2 = y * y;
    let x2 = (y2 - BF_ONE) * inv(D * y2 + BF_ONE);

    // Find the square root of x2 if there is one, other return None
    let mut x = match sqrt(&x2) {
      Some(x) => x,
      None => return None,
    };

    // There is only one correct value of sign of '0' in the basefield.
    if x == BF_ZERO && get_sign_bit(&x) != xsign {
      return None;
    }

    // Correct the sign of x.
    if get_sign_bit(&x) != xsign {
      x = -x;
    }

    Some(Coordinate::new(x, y))
  }
}

impl PartialEq for Coordinate {
  /// Checks for equality of two `Coordinate` points on the Ed25519 curve.
  fn eq(&self, other: &Self) -> bool {
    // Convert the extended homogeneous coordinates to affine coordinates before comparison.
    let x1 = self.x * inv(self.z);
    let y1 = self.y * inv(self.z);

    let x2 = other.x * inv(other.z);
    let y2 = other.y * inv(other.z);

    (x1 == x2) && (y1 == y2)
  }
}

impl Add for Coordinate {
  type Output = Self;

  /// Adds two `Coordinate` points on the Ed25519 curve.
  ///
  /// This implementation uses the efficient extended homogeneous coordinates addition formula
  /// from Section 3.2 of [EdwardsRevisited] to avoid expensive field inversions.
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
  /// Adds another `Coordinate` point to the current point in-place.
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl Mul<ScalarField> for Coordinate {
  type Output = Self;

  /// Performs scalar multiplication on a `Coordinate` point.
  ///
  /// This implementation uses the double-and-add algorithm for efficient scalar multiplication.
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
