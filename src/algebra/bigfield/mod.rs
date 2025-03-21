pub mod bigint;

use std::{
  marker::PhantomData,
  ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use bigint::{BigInt, BYTES};

#[macro_export]
macro_rules! create_modulus {
  ($name:ident, $type:ty, $modulus:expr) => {
    use crate::algebra::bigfield::bigint::*;

    #[derive(Debug)]
    pub struct $name;

    impl Modulus<$type> for $name {
      const M: $type = <$type>::from_be_bytes($modulus);

      fn reduce(xt: ($type, $type)) -> $type {
        const MU: Concat<$type> = Concat::from_le_bytes(calculate_mu(&<$name>::M).to_le_bytes());

        let x = Concat::new(&xt.0, &xt.1);

        let q1 = x.shr(<$type>::BITS - Word::BITS);

        let (q2_r, q2_c) = q1.widening_mul(&MU);
        let q3 = Concat::new(&q2_r.split().1, &q2_c.split().0).shr(Word::BITS);

        // mask = (1 << 320) - 1;
        let mask = Concat::new(&BigInt::ZERO, &BigInt::pow_of_2(Word::BITS)).sub(&Concat::ONE);

        let r1 = x.bitwise_and(&mask);

        const M_PAD: Concat<$type> = Concat::<$type>::new(&<$name>::M, &<$type>::ZERO);
        let mut r2 = q3.mul_half(&Self::M);
        r2 = r2.bitwise_and(&mask);

        let mut r = match r1.lt(&r2) {
          true => {
            let t = r1.carrying_add(&mask, true);
            t.0.sub(&r2)
          },
          false => r1.sub(&r2),
        };

        let mut i = 0;
        while i < 2 && r.gt(&M_PAD) {
          r = r.sub(&M_PAD);
          i += 1;
        }

        let (lo, _hi) = r.split();
        lo
      }
    }
  };
}

#[macro_export]
macro_rules! create_special_modulus_type_1 {
  ($name:ident, $type:ty, $t:expr, $c:expr) => {
    use crate::algebra::bigfield::bigint::*;

    pub struct $name;
    impl Modulus<$type> for $name {
      const M: $type = {
        const BT: $type = <$type>::pow_of_2($t);
        const C: $type = <$type>::from_u64($c);

        BT.sub(&C)
      };

      fn reduce(xt: ($type, $type)) -> $type {
        let x = Concat::<$type>::new(&xt.0, &xt.1);
        let mut q0 = x.shr($t);
        let r0 = x.sub(&q0.shl($t));
        let mut r = r0;

        while q0.gt(&Concat::<$type>::ZERO) {
          let q0_c = q0.mul_word($c);
          let q1 = q0_c.shr($t);

          let r1 = q0_c.sub(&q1.shl($t));

          let r2 = r.add(&r1);
          r = r2;

          q0 = q1;
        }

        const M_PAD: Concat<$type> = Concat::<$type>::new(&<$name>::M, &<$type>::ZERO);
        while r.gt(&M_PAD) {
          r = r.sub(&M_PAD);
        }

        let (lo, _hi) = r.split();
        lo
      }
    }
  };
}

#[macro_export]
macro_rules! create_special_modulus_type_2 {
  ($name:ident, $type:ty, $t:expr, $c:expr) => {
    pub struct $name;
    impl Modulus<$type> for $name {
      const M: $type = {
        const BT: $type = <$type>::pow_of_2($t);
        const C: $type = <$type>::from_be_bytes($c);

        BT.add(&C)
      };

      fn reduce(xt: ($type, $type)) -> $type {
        const C: $type = <$type>::from_be_bytes($c);

        let x = Concat::<$type>::new(&xt.0, &xt.1);
        let mut q0 = x.shr($t);
        let r0 = x.sub(&q0.shl($t));
        let mut rp = r0;
        let mut rn = Concat::ZERO;

        let mut flag = true;

        while q0.gt(&Concat::<$type>::ZERO) {
          let q0_c = q0.mul_half(&C);
          let q1 = q0_c.shr($t);

          let r1 = q0_c.sub(&q1.shl($t));

          match flag {
            true => rn = rn.add(&r1),
            false => rp = rp.add(&r1),
          };

          q0 = q1;
          flag = !flag;
        }

        const M_PAD: Concat<$type> = Concat::<$type>::new(&<$name>::M, &<$type>::ZERO);

        let mut r = match rp.lt(&rn) {
          true => rp.add(&M_PAD).sub(&rn),
          false => rp.sub(&rn),
        };

        let mut i = 0;
        while i < 2 && !r.lt(&M_PAD) {
          r = r.sub(&M_PAD);
          i += 1;
        }

        let (lo, _hi) = r.split();
        lo
      }
    }
  };
}

pub trait Modulus<T> {
  const M: T;
  fn reduce(x: (T, T)) -> T;
}

pub struct PrimeField<T, P: Modulus<T>> {
  pub(crate) value: T,
  phantom:          PhantomData<P>,
}

impl<const N: usize, P: Modulus<BigInt<N>>> Clone for PrimeField<BigInt<N>, P> {
  fn clone(&self) -> Self { Self { value: self.value.clone(), phantom: PhantomData } }
}

impl<const N: usize, P: Modulus<BigInt<N>>> Copy for PrimeField<BigInt<N>, P> {}

impl<const N: usize, P: Modulus<BigInt<N>>> PrimeField<BigInt<N>, P> {
  const ONE: PrimeField<BigInt<N>, P> = Self { value: BigInt::from_u64(1), phantom: PhantomData };
  const ZERO: PrimeField<BigInt<N>, P> =
    Self { value: BigInt::from_u64(0), phantom: PhantomData };

  pub const fn to_le_bytes(self) -> [u8; N * BYTES] { self.value.to_le_bytes() }

  pub const fn to_be_bytes(self) -> [u8; N * BYTES] { self.value.to_be_bytes() }

  pub const fn eq(self, other: &Self) -> bool { self.value.eq(&other.value) }

  pub const fn is_even(self) -> bool { (self.value.to_words()[0] & 1) == 0 }

  pub const fn is_odd(self) -> bool { !self.is_even() }

  pub fn pow(self, exp: &BigInt<N>) -> Self
  where [(); N * 2]: {
    if exp.eq(&BigInt::<N>::ZERO) {
      Self::ONE
    } else if exp.is_even() {
      let a = self.pow(&exp.shr(1).0);
      a * a
    } else {
      let a = self.pow(&exp.shr(1).0);
      a * a * self
    }
  }

  pub fn inv(self) -> Option<Self>
  where [(); N * 2]: {
    if self.eq(&Self::ZERO) {
      return None;
    }

    Some(self.pow(&P::M.sub(&BigInt::from_u64(2))))
  }

  pub fn euler_criterion(&self) -> bool
  where [(); N * 2]: {
    self.pow(&(P::M.sub(&BigInt::<N>::ONE)).shr(1).0).eq(&Self::ONE)
  }

  /// Computes the square root of a field element using the [Tonelli-Shanks algorithm](https://en.wikipedia.org/wiki/Tonelli–Shanks_algorithm).
  pub fn sqrt(&self) -> Option<(Self, Self)>
  where [(); N * 2]: {
    if self.eq(&Self::ZERO) {
      return Some((Self::ZERO, Self::ZERO));
    }

    if !self.euler_criterion() {
      return None;
    }

    // First define the Q and S values for the prime number P.
    let mut q = P::M.sub(&BigInt::ONE);
    let mut s = 0;
    while q.is_even() {
      q = q.shr(1).0;
      s += 1;
    }

    // Find a z that is not a quadratic residue
    let mut z = Self::from(2u32);
    while z.euler_criterion() {
      z += Self::ONE;
    }
    let mut m = s;
    let mut c = z.pow(&q);
    let mut t = self.pow(&q);
    let mut r = self.pow(&(q.add(&BigInt::ONE)).shr(1).0);
    loop {
      if t.eq(&Self::ONE) {
        if (-r).value.lt(&r.value) {
          return Some((-r, r));
        } else {
          return Some((r, -r));
        }
      }
      // Repeatedly square to find a t^2^i = 1
      let mut i = 1;
      let mut t_pow = t.pow(&BigInt::from(2u32));
      while !t_pow.eq(&Self::ONE) {
        t_pow = t_pow.pow(&BigInt::from(2u32));
        i += 1;
      }
      let b = c.pow(&BigInt::pow_of_2(m - i - 1));
      m = i;
      c = b.pow(&BigInt::from(2u32));
      t *= c;
      r *= b;
    }
  }
}

impl<const N: usize, P: Modulus<BigInt<N>>> From<BigInt<N>> for PrimeField<BigInt<N>, P> {
  fn from(value: BigInt<N>) -> Self {
    let mut reduced_value = value;
    if !value.lt(&P::M) {
      let value_padded = (value, BigInt::<N>::ZERO);
      reduced_value = P::reduce(value_padded);
    }

    Self { value: reduced_value, phantom: PhantomData }
  }
}

impl<const N: usize, P: Modulus<BigInt<N>>> From<(BigInt<N>, BigInt<N>)>
  for PrimeField<BigInt<N>, P>
{
  fn from(value: (BigInt<N>, BigInt<N>)) -> Self {
    Self { value: P::reduce(value), phantom: PhantomData }
  }
}

impl<const N: usize, P: Modulus<BigInt<N>>> From<u64> for PrimeField<BigInt<N>, P> {
  fn from(value: u64) -> Self { Self::from(BigInt::from_u64(value)) }
}

impl<const N: usize, P: Modulus<BigInt<N>>> From<u32> for PrimeField<BigInt<N>, P> {
  fn from(value: u32) -> Self { Self::from(BigInt::from_u32(value)) }
}

impl<const N: usize, P: Modulus<BigInt<N>>> Add for PrimeField<BigInt<N>, P> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    let (r, c) = self.value.carrying_add(&rhs.value, false);
    if c || !r.lt(&P::M) {
      return Self { value: r.sub(&P::M), phantom: PhantomData };
    }
    Self { value: r, phantom: PhantomData }
  }
}

impl<const N: usize, P: Modulus<BigInt<N>>> AddAssign for PrimeField<BigInt<N>, P> {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<const N: usize, P: Modulus<BigInt<N>>> Sub for PrimeField<BigInt<N>, P> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self::Output {
    let mut r = self.value;
    if r.lt(&rhs.value) {
      let r0 = r.add(&P::M);
      r = r0;
    }
    let r1 = r.sub(&rhs.value);
    Self { value: r1, phantom: PhantomData }
  }
}

impl<const N: usize, P: Modulus<BigInt<N>>> SubAssign for PrimeField<BigInt<N>, P> {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<const N: usize, P: Modulus<BigInt<N>>> Mul for PrimeField<BigInt<N>, P>
where [(); N * 2]:
{
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    let (u, v) = self.value.widening_mul(&rhs.value);
    let x = P::reduce((u, v));
    Self { value: x, phantom: PhantomData }
  }
}

impl<const N: usize, P: Modulus<BigInt<N>>> MulAssign for PrimeField<BigInt<N>, P>
where [(); N * 2]:
{
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<const N: usize, P: Modulus<BigInt<N>>> Neg for PrimeField<BigInt<N>, P> {
  type Output = Self;

  fn neg(self) -> Self::Output { Self { value: P::M.sub(&self.value), phantom: PhantomData } }
}

#[cfg(test)]
mod tests {
  use crypto_bigint::{
    impl_modulus,
    modular::{ConstMontyForm, ConstMontyParams, Retrieve},
    Encoding, U256, U512,
  };
  use hex_literal::hex;
  use rand::Rng;
  use rstest::rstest;

  use super::*;

  create_special_modulus_type_1!(P0, BigInt<4>, 255, 19);
  create_modulus!(
    L0,
    BigInt<4>,
    hex!("1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed")
  );

  impl_modulus!(P1, U256, "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed");
  impl_modulus!(
        P2,
        U512,
        "0000000000000000000000000000000000000000000000000000000000000000\
        7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
    );

  impl_modulus!(L1, U256, "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed");
  impl_modulus!(
        L2,
        U512,
        "0000000000000000000000000000000000000000000000000000000000000000\
        1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"
    );

  type F0 = PrimeField<BigInt<4>, P0>;
  type F1 = ConstMontyForm<P1, { U256::LIMBS }>;
  type F2 = ConstMontyForm<P2, { U512::LIMBS }>;

  type F3 = PrimeField<BigInt<4>, L0>;
  type F4 = ConstMontyForm<L1, { U256::LIMBS }>;
  type F5 = ConstMontyForm<L2, { U512::LIMBS }>;

  #[test]
  fn test_reduction_random() {
    let mut rng = rand::thread_rng();
    for _i in 0..10000 {
      let bytes: [u8; 32] =
        (0..32).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let a1 = BigInt::<4>::from_le_bytes(bytes);

      let a2 = U256::from_le_bytes(bytes);

      let actual1 = F0::from(a1).to_le_bytes();
      let actual2 = F3::from(a1).to_le_bytes();

      let expected1 = F1::new(&a2).retrieve().to_le_bytes();
      let expected2 = F4::new(&a2).retrieve().to_le_bytes();

      assert_eq!(actual1, expected1);
      assert_eq!(actual2, expected2);
    }
  }
  #[test]
  fn test_concat_reduction() {
    let mut rng = rand::thread_rng();
    for _i in 0..10000 {
      let bytes: [u8; 64] =
        (0..64).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let u = BigInt::<4>::from_le_bytes(bytes[..32].try_into().unwrap());
      let v = BigInt::<4>::from_le_bytes(bytes[32..].try_into().unwrap());

      let actual1 = F0::from((u, v)).to_le_bytes();
      let actual2 = F3::from((u, v)).to_le_bytes();

      let expected1: [u8; 32] =
        F2::new(&U512::from_le_bytes(bytes)).retrieve().to_le_bytes()[..32].try_into().unwrap();

      let expected2: [u8; 32] =
        F5::new(&U512::from_le_bytes(bytes)).retrieve().to_le_bytes()[..32].try_into().unwrap();

      assert_eq!(actual1, expected1);
      assert_eq!(actual2, expected2);
    }
  }

  #[test]
  fn test_add_sub_mul() {
    let mut rng = rand::thread_rng();
    for _i in 0..10000 {
      let bytes: [u8; 64] =
        (0..64).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let u = F0::from(BigInt::<4>::from_le_bytes(bytes[..32].try_into().unwrap()));
      let v = F0::from(BigInt::<4>::from_le_bytes(bytes[32..].try_into().unwrap()));

      let u1 = F3::from(BigInt::<4>::from_le_bytes(bytes[..32].try_into().unwrap()));
      let v1 = F3::from(BigInt::<4>::from_le_bytes(bytes[32..].try_into().unwrap()));

      let w1 = u * v;
      let w2 = u + v;
      let w3 = u - v;

      let mut w4 = u;
      w4 += v;
      w4 *= v;
      w4 -= v;

      let x1 = u1 * v1;
      let x2 = u1 + v1;
      let x3 = u1 - v1;

      let mut x4 = u1;
      x4 += v1;
      x4 *= v1;
      x4 -= v1;

      let p = F1::new(&U256::from_le_bytes(bytes[..32].try_into().unwrap()));
      let q = F1::new(&U256::from_le_bytes(bytes[32..].try_into().unwrap()));

      let p1 = F4::new(&U256::from_le_bytes(bytes[..32].try_into().unwrap()));
      let q1 = F4::new(&U256::from_le_bytes(bytes[32..].try_into().unwrap()));

      let r1 = p * q;
      let r2 = p + q;
      let r3 = p - q;

      let mut r4 = p;
      r4 += q;
      r4 *= q;
      r4 -= q;

      let t1 = p1 * q1;
      let t2 = p1 + q1;
      let t3 = p1 - q1;

      let mut t4 = p1;
      t4 += q1;
      t4 *= q1;
      t4 -= q1;

      let actual1 = w1.to_le_bytes();
      let actual2 = w2.to_le_bytes();
      let actual3 = w3.to_le_bytes();
      let actual4 = w4.to_le_bytes();

      let actual5 = x1.to_le_bytes();
      let actual6 = x2.to_le_bytes();
      let actual7 = x3.to_le_bytes();
      let actual8 = x4.to_le_bytes();

      let expected1 = r1.retrieve().to_le_bytes();
      let expected2 = r2.retrieve().to_le_bytes();
      let expected3 = r3.retrieve().to_le_bytes();
      let expected4 = r4.retrieve().to_le_bytes();

      let expected5 = t1.retrieve().to_le_bytes();
      let expected6 = t2.retrieve().to_le_bytes();
      let expected7 = t3.retrieve().to_le_bytes();
      let expected8 = t4.retrieve().to_le_bytes();

      assert_eq!(actual1, expected1);
      assert_eq!(actual2, expected2);
      assert_eq!(actual3, expected3);
      assert_eq!(actual4, expected4);

      assert_eq!(actual5, expected5);
      assert_eq!(actual6, expected6);
      assert_eq!(actual7, expected7);
      assert_eq!(actual8, expected8);
    }
  }

  #[test]
  fn test_pow() {
    let mut rng = rand::thread_rng();

    for _i in 0..1000 {
      let bytes: [u8; 64] =
        (0..64).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let base1 = F0::from(BigInt::<4>::from_le_bytes(bytes[..32].try_into().unwrap()));
      let exp1 = BigInt::<4>::from_le_bytes(bytes[32..].try_into().unwrap());
      let exp1a = BigInt::<4>::from_u64(_i);

      let res1 = base1.pow(&exp1);
      let res1a = base1.pow(&exp1a);

      let base2 = F1::new(&U256::from_le_bytes(bytes[..32].try_into().unwrap()));
      let exp2 = U256::from_le_bytes(bytes[32..].try_into().unwrap());
      let exp2a = U256::from_u64(_i);

      let res2 = base2.pow(&exp2);
      let res2a = base2.pow(&exp2a);

      let base3 = F3::from(BigInt::<4>::from_le_bytes(bytes[..32].try_into().unwrap()));
      let exp3 = BigInt::<4>::from_le_bytes(bytes[32..].try_into().unwrap());
      let exp3a = BigInt::<4>::from_u64(_i);

      let res3 = base1.pow(&exp1);
      let res3a = base1.pow(&exp1a);

      let base4 = F4::new(&U256::from_le_bytes(bytes[..32].try_into().unwrap()));
      let exp4 = U256::from_le_bytes(bytes[32..].try_into().unwrap());
      let exp4a = U256::from_u64(_i);

      let res4 = base2.pow(&exp2);
      let res4a = base2.pow(&exp2a);

      let actual1 = base1.to_le_bytes();
      let actual2 = exp1.to_le_bytes();
      let actual3 = exp1a.to_le_bytes();
      let actual4 = res1.to_le_bytes();
      let actual5 = res1a.to_le_bytes();

      let actual6 = base3.to_le_bytes();
      let actual7 = exp3.to_le_bytes();
      let actual8 = exp3a.to_le_bytes();
      let actual9 = res3.to_le_bytes();
      let actual10 = res3a.to_le_bytes();

      let expected1 = base2.retrieve().to_le_bytes();
      let expected2 = exp2.to_le_bytes();
      let expected3 = exp2a.to_le_bytes();
      let expected4 = res2.retrieve().to_le_bytes();
      let expected5 = res2a.retrieve().to_le_bytes();

      let expected6 = base4.retrieve().to_le_bytes();
      let expected7 = exp4.to_le_bytes();
      let expected8 = exp4a.to_le_bytes();
      let expected9 = res4.retrieve().to_le_bytes();
      let expected10 = res4a.retrieve().to_le_bytes();

      assert_eq!(actual1, expected1);
      assert_eq!(actual2, expected2);
      assert_eq!(actual3, expected3);
      assert_eq!(actual4, expected4);
      assert_eq!(actual5, expected5);

      assert_eq!(actual6, expected6);
      assert_eq!(actual7, expected7);
      assert_eq!(actual8, expected8);
      assert_eq!(actual9, expected9);
      assert_eq!(actual10, expected10);
    }
  }

  #[test]
  fn test_inv() {
    const P_2: U256 =
      U256::from_be_hex("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb");
    const L_2: U256 =
      U256::from_be_hex("1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3eb");

    let mut rng = rand::thread_rng();
    for _i in 0..1000 {
      let bytes: [u8; 32] =
        (0..32).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      // by off chance :)
      if bytes == [0u8; 32] {
        continue;
      }

      let base1 = F0::from(BigInt::<4>::from_le_bytes(bytes));
      let base2 = F1::new(&U256::from_le_bytes(bytes));

      let base3 = F3::from(BigInt::<4>::from_le_bytes(bytes));
      let base4 = F4::new(&U256::from_le_bytes(bytes));

      let inv1 = base1.inv().unwrap();
      let inv2 = base2.pow(&P_2);
      let inv3 = base2.inv().unwrap();

      let inv4 = base3.inv().unwrap();
      let inv5 = base4.pow(&L_2);
      let inv6 = base4.inv().unwrap();

      let actual1 = inv1.to_le_bytes();
      let actual2 = inv4.to_le_bytes();

      let expected1a = inv2.retrieve().to_le_bytes();
      let expected1b = inv3.retrieve().to_le_bytes();

      let expected2a = inv5.retrieve().to_le_bytes();
      let expected2b = inv6.retrieve().to_le_bytes();

      assert_eq!(actual1, expected1a);
      assert_eq!(actual1, expected1b);

      assert_eq!(actual2, expected2a);
      assert_eq!(actual2, expected2b);
    }
  }

  /// Find the square root of an element of the `F1`
  /// It uses the algorithm given in Section 5.1.1 of [RFC8032] utilizing the special case of
  /// `P = 5 (mod 8)`. To read more, see: (https://en.wikipedia.org/wiki/Quadratic_residue#Prime_or_prime_power_modulus)
  pub fn sqrt(x: &F1) -> Option<F1> {
    const TWO: U256 = U256::from_u8(2u8);
    const THREE: U256 = U256::from_u8(3u8);

    let mut exp = (P1::MODULUS.get() + THREE).shr(3);
    let y1 = x.pow(&exp);

    if y1 * y1 == *x {
      return Some(y1);
    }

    exp = (P1::MODULUS.get() - U256::ONE).shr(2);
    let z = F1::new(&TWO).pow(&exp);
    let y2 = y1 * z;
    if y2 * y2 == *x {
      return Some(y2);
    } else {
      return None;
    }
  }

  #[test]
  fn test_sqrt() {
    let mut rng = rand::thread_rng();
    for _i in 0..1000 {
      let bytes: [u8; 32] =
        (0..32).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();
      let p = F0::from(BigInt::from_le_bytes(bytes));

      let r = p.sqrt();

      let a = F1::new(&U256::from_le_bytes(bytes));

      let c = sqrt(&a);

      match (r, c) {
        (Some(x), Some(y)) => {
          let y1 = match y.neg().retrieve() < y.retrieve() {
            true => y,
            false => y.neg(),
          };
          assert_eq!(x.1.to_le_bytes(), y1.retrieve().to_le_bytes());
        },
        (None, None) => assert!(true),

        // written separately to help debug
        (None, _) => assert!(false),
        (_, None) => assert!(false),
      }
    }
  }
}
