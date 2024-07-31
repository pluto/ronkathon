//! Implements [dihedral][dihedral] group of degree 3 and order 6 using ronkathon's [`Group`] and
//! [`FiniteGroup`] trait.
//!
//! Consider a symmetric group containing all permutation of 3 distinct
//! elements: `[a, b, c]`. Total number of elements is 3! = 6. Each element of the group is a
//! permutation operation.
//!
//! ## Example
//! Let `a=[2, 1, 3]` be an element of the group, when applied to any 3-length vector performs the
//! swap of 1st and 2nd element. So, `RGB->GRB`.
//!
//! ## Operation
//! Group operation is defined as combined action of performing permutation twice, i.e. take `x,y`
//! two distinct element of the group. `a·b` is applying permutation `b` first then `a`.
//!
//! [dihedral]: https://en.wikipedia.org/wiki/Dihedral_group_of_order_6
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use ronkathon::algebra::{
  group::{FiniteGroup, Group},
  Finite,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DihedralGroup {
  mapping: [usize; 3],
}

impl Finite for DihedralGroup {
  const ORDER: usize = 6;
}

impl Group for DihedralGroup {
  type Scalar = usize;

  const IDENTITY: Self = Self::new([0, 1, 2]);

  fn op(&self, rhs: &Self) -> Self {
    let mut new_mapping = [0; 3];
    for (i, &j) in self.mapping.iter().enumerate() {
      new_mapping[i] = rhs.mapping[j];
    }

    Self::new(new_mapping)
  }

  fn inverse(&self) -> Option<Self> {
    let mut inverse_mapping = [0; 3];
    for (i, &j) in self.mapping.iter().enumerate() {
      inverse_mapping[j] = i;
    }

    Some(Self::new(inverse_mapping))
  }

  fn scalar_mul(&self, scalar: Self::Scalar) -> Self {
    let mut res = *self;
    for _ in 0..scalar {
      res = res.op(self);
    }
    res
  }
}

impl DihedralGroup {
  const fn new(mapping: [usize; 3]) -> Self { Self { mapping } }
}

impl FiniteGroup for DihedralGroup {}

impl Default for DihedralGroup {
  fn default() -> Self { Self::IDENTITY }
}

impl Add for DihedralGroup {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output { Self::op(&self, &rhs) }
}

impl AddAssign for DihedralGroup {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl Neg for DihedralGroup {
  type Output = Self;

  fn neg(self) -> Self::Output { Self::inverse(&self).expect("inverse does not exist") }
}

impl Sub for DihedralGroup {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self::Output { self + -rhs }
}

impl SubAssign for DihedralGroup {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl Mul<usize> for DihedralGroup {
  type Output = Self;

  fn mul(self, rhs: usize) -> Self::Output { Self::scalar_mul(&self, rhs) }
}

impl MulAssign<usize> for DihedralGroup {
  fn mul_assign(&mut self, rhs: usize) { *self = *self * rhs; }
}

fn main() {
  let ident = DihedralGroup::default();
  let a = DihedralGroup::new([1, 0, 2]);
  let b = DihedralGroup::new([0, 2, 1]);

  // closure
  let ab = a.op(&b);
  let ba = b.op(&a);

  // identity
  assert_eq!(a, ident.op(&a));
  assert_eq!(b, ident.op(&b));

  // non-abelian property
  assert_ne!(ab, ba);

  // group element order
  assert_eq!(a.order(), 2);
  assert_eq!(ab.order(), 3);
  assert_eq!(ba.order(), 3);

  // inverse
  assert_eq!(a.op(&a.inverse().unwrap()), ident);
  assert_eq!(ab.inverse().unwrap(), ba);
}
