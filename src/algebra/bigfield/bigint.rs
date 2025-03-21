pub type Word = u64;
pub type DWord = u128;
pub const BYTES: usize = 8; // Number of bytes in each 'Word'

#[derive(Debug, Clone, Copy)]
pub struct BigInt<const N: usize>([Word; N]);

impl<const N: usize> BigInt<N> {
  pub const BITS: u32 = N as u32 * Word::BITS;
  pub const ONE: BigInt<N> = BigInt::<N>::from_u64(1);
  pub const ZERO: BigInt<N> = BigInt([0 as Word; N]);

  pub const fn from_u32(value: u32) -> Self {
    let mut limbs = [0 as Word; N];
    limbs[0] = value as Word;
    Self(limbs)
  }

  pub const fn from_u64(value: u64) -> Self {
    let mut limbs = [0 as Word; N];
    limbs[0] = value as Word;
    Self(limbs)
  }

  pub const fn pow_of_2(pos: u32) -> Self {
    assert!((pos as usize) < N * (Word::BITS as usize));
    let mut limbs = [0 as Word; N];
    let limb = pos / Word::BITS;

    limbs[limb as usize] = 1 << (pos % Word::BITS);

    Self(limbs)
  }

  pub const fn from_le_bytes(bytes: [u8; N * 8]) -> Self {
    let mut limbs = [0 as Word; N];
    let mut i = 0;

    while i < N {
      let mut j = i * 8;
      let mut value = 0 as Word;
      let mut mag = 1;
      while j < 8 * (i + 1) {
        value += mag * (bytes[j] as u64);
        mag = mag << 8;
        j += 1;
      }
      limbs[i] = value;
      i += 1;
    }

    Self(limbs)
  }

  pub const fn from_be_bytes(bytes: [u8; N * 8]) -> Self {
    let mut limbs = [0 as Word; N];
    let mut i = 0;

    while i < N {
      let mut j = i * 8;
      let mut value = 0 as Word;
      let mut mag = 1;
      while j < 8 * (i + 1) {
        value += mag * (bytes[(N * 8 - 1) - j] as u64);
        mag = mag << 8;
        j += 1;
      }
      limbs[i] = value;
      i += 1;
    }

    Self(limbs)
  }

  pub const fn to_le_bytes(&self) -> [u8; N * BYTES] {
    let mut bytes = [0u8; N * BYTES];
    let mut i = 0;
    while i < N {
      let mut j = 0;
      while j < BYTES {
        bytes[8 * i + j] = ((self.0[i] >> 8 * j) & ((1 << 8) - 1)) as u8;
        j += 1;
      }
      i += 1;
    }

    bytes
  }

  pub const fn to_be_bytes(&self) -> [u8; N * BYTES] {
    let mut bytes = [0u8; N * BYTES];
    let mut i = 0;
    while i < N {
      let mut j = 0;
      while j < BYTES {
        bytes[8 * i + j] = ((self.0[N - 1 - i] >> 8 * (BYTES - j - 1)) & ((1 << 8) - 1)) as u8;
        j += 1;
      }
      i += 1;
    }

    bytes
  }

  pub const fn to_words(&self) -> [Word; N] { self.0 }

  pub const fn eq(&self, rhs: &Self) -> bool {
    let mut i = 0;
    while i < N {
      if self.0[i] != rhs.0[i] {
        return false;
      }
      i += 1;
    }
    true
  }

  pub const fn neq(&self, rhs: &Self) -> bool { !self.eq(rhs) }

  pub const fn gt(&self, rhs: &Self) -> bool {
    let mut i = N;
    while i > 0 && self.0[i - 1] == rhs.0[i - 1] {
      i -= 1;
    }

    if i > 0 {
      return self.0[i - 1] > rhs.0[i - 1];
    }
    false
  }

  pub const fn lt(&self, rhs: &Self) -> bool {
    let mut i = N;
    while i > 0 && self.0[i - 1] == rhs.0[i - 1] {
      i -= 1;
    }

    if i > 0 {
      return self.0[i - 1] < rhs.0[i - 1];
    }
    false
  }

  pub const fn carrying_add(&self, rhs: &Self, mut carry: bool) -> (Self, bool) {
    let mut i = 0;
    let mut res = [0 as Word; N];
    while i < N {
      let (sum, _carry) = self.0[i].carrying_add(rhs.0[i], carry);
      res[i] = sum;
      carry = _carry;
      i += 1;
    }

    (Self(res), carry)
  }

  pub const fn borrowing_sub(&self, rhs: &Self, mut borrow: bool) -> (Self, bool) {
    let mut res = [0 as Word; N];
    let mut i = 0;
    while i < N {
      let (sum, _borrow) = self.0[i].borrowing_sub(rhs.0[i], borrow);
      res[i] = sum;
      borrow = _borrow;
      i += 1;
    }

    (Self(res), borrow)
  }

  pub const fn widening_mul(&self, rhs: &Self) -> (Self, Self)
  where [(); N * 2]: {
    let mut w = [0 as Word; N * 2];
    let mut i = 0;
    while i < N {
      let mut carry = 0 as Word;
      let mut j = 0;
      while j < N {
        let (mul, carry0) = self.0[j].carrying_mul(rhs.0[i], carry);
        let (sum, carry1) = w[i + j].carrying_add(mul, false);
        w[i + j] = sum;
        carry = carry0 + carry1 as u64;
        j += 1;
      }
      w[i + N] = carry;
      i += 1;
    }

    i = 0;
    let mut res = [0 as Word; N];
    let mut carry = [0 as Word; N];
    while i < N {
      res[i] = w[i];
      i += 1;
    }
    while i < 2 * N {
      carry[i - N] = w[i];
      i += 1;
    }

    (Self(res), Self(carry))
  }

  pub const fn bitwise_or(&self, rhs: &Self) -> Self {
    let mut limbs = [0 as Word; N];

    let mut i = 0;
    while i < N {
      limbs[i] = self.0[i] | rhs.0[i];
      i += 1;
    }

    Self(limbs)
  }

  pub const fn bitwise_and(&self, rhs: &Self) -> Self {
    let mut limbs = [0 as Word; N];

    let mut i = 0;
    while i < N {
      limbs[i] = self.0[i] & rhs.0[i];
      i += 1;
    }

    Self(limbs)
  }

  pub const fn shr(&self, shift: u32) -> (Self, Self) {
    assert!((shift as usize) < N * Word::BITS as usize);

    let shiftq = (shift / Word::BITS) as usize;
    let shiftr = (shift % Word::BITS) as usize;
    let mut limbs = [0 as Word; N];
    let mut i = N;
    let mut borrow = 0 as Word;

    while i > shiftq {
      if shiftr != 0 {
        limbs[i - 1 - shiftq] = (self.0[i - 1] >> shiftr) | borrow;
        borrow = (self.0[i - 1] & ((1 << shiftr) - 1)) << (Word::BITS - shiftr as u32);
      } else {
        limbs[i - 1 - shiftq] = self.0[i - 1];
      }
      i -= 1;
    }

    let mut borrow_limbs = [0 as Word; N];

    while i > 0 {
      if shiftr != 0 {
        borrow_limbs[N - 1 + i - shiftq] = (self.0[i - 1] >> shiftr) | borrow;
        borrow = (self.0[i - 1] & ((1 << shiftr) - 1)) << (Word::BITS - shiftr as u32);
      } else {
        borrow_limbs[N - 1 + i - shiftq] = self.0[i - 1];
      }

      i -= 1;
    }
    borrow_limbs[N - 1 - shiftq] = borrow;

    (Self(limbs), Self(borrow_limbs))
  }

  pub const fn shl(&self, shift: u32) -> (Self, Self) {
    assert!((shift as usize) < N * Word::BITS as usize);

    let shiftq = (shift / Word::BITS) as usize;
    let shiftr = shift % Word::BITS;
    let mut limbs = [0 as Word; N];
    let mut i = shiftq;
    let mut carry = 0 as Word;

    while i < N {
      if shiftr != 0 {
        limbs[i] = (self.0[i - shiftq] << shiftr) | carry;
        carry = (self.0[i - shiftq] & !((1 << (Word::BITS - shiftr)) - 1)) >> Word::BITS - shiftr;
      } else {
        limbs[i] = self.0[i - shiftq];
      }
      i += 1;
    }

    let mut carry_limbs = [0 as Word; N];
    let mut j = N - shiftq;
    while j < N {
      if shiftr != 0 {
        carry_limbs[j + shiftq - N] = (self.0[j] << shiftr) | carry;
        carry = (self.0[j] & !((1 << (Word::BITS - shiftr)) - 1)) >> Word::BITS - shiftr;
      } else {
        carry_limbs[j + shiftq - N] = self.0[j];
      }
      j += 1;
    }
    carry_limbs[shiftq] = carry;

    (Self(limbs), Self(carry_limbs))
  }

  pub const fn add(&self, rhs: &Self) -> Self { self.carrying_add(rhs, false).0 }

  pub const fn sub(&self, rhs: &Self) -> Self { self.borrowing_sub(rhs, false).0 }

  #[inline]
  pub const fn is_even(&self) -> bool { (self.0[0] & 1) == 0 }

  pub const fn carrying_mul_word(&self, rhs: Word, mut carry: Word) -> (Self, Word) {
    let mut w = [0 as Word; N];
    let mut i = 0;

    while i < N {
      let (mul, carry0) = self.0[i].carrying_mul(rhs, carry);
      let (sum, carry1) = w[i].carrying_add(mul, false);
      w[i] = sum;
      carry = carry0 + carry1 as u64;
      i += 1;
    }

    (Self(w), carry)
  }
}

impl<const N: usize> From<u64> for BigInt<N> {
  fn from(value: u64) -> Self { Self::from_u64(value) }
}

impl<const N: usize> From<u32> for BigInt<N> {
  fn from(value: u32) -> Self { Self::from_u32(value) }
}

pub const fn calculate_mu<const N: usize>(m: &BigInt<N>) -> BigInt<{ 2 * N }>
where [(); 2 * N]: {
  assert!(m.0[N - 1] > 1);

  let mut q = [0 as Word; 2 * N];

  let mut x = BigInt::<{ 2 * N }>::ZERO;
  let mut y_words = [0 as Word; 2 * N];
  let mut i = 0;
  while i < N {
    y_words[i] = m.0[i];
    i += 1;
  }

  let y = BigInt(y_words);

  let b = (1 as DWord) << Word::BITS;
  let c = b / y.0[N - 1] as DWord;
  q[N] = c as Word;

  while (q[N] as DWord).checked_mul((y.0[N - 1] as DWord) * b + (y.0[N - 2] as DWord)).is_none() {
    q[N] -= 1;
  }

  let mut x1 = y.shl(N as u32 * Word::BITS).0;
  let mut x2 = x1.carrying_mul_word(q[N], 0).0;
  x = x.sub(&x2);

  i = 2 * N - 1;
  while i >= N {
    q[i - N] = match x.0[i] == y.0[N - 1] {
      true => (b - 1) as Word,
      false => ((x.0[i] as DWord * b + x.0[i - 1] as DWord) / y.0[N - 1] as DWord) as Word,
    };

    while BigInt::from_u64(q[i - N])
      .widening_mul(&BigInt([y.0[N - 2], y.0[N - 1], 0, 0]))
      .0
      .gt(&BigInt([x.0[i - 2], x.0[i - 1], x.0[i], 0]))
    {
      q[i - N] -= 1;
    }

    x1 = y.shl((i - N) as u32 * Word::BITS).0;
    x2 = x1.carrying_mul_word(q[i - N], 0).0;
    x = match x.lt(&x2) {
      true => {
        q[i - N] -= 1;
        x.add(&x1).sub(&x2)
      },
      false => x.sub(&x2),
    };

    i -= 1;
  }

  BigInt(q)
}

#[derive(Debug, Clone, Copy)]
pub struct Concat<T>(T, T);

impl<const N: usize> Concat<BigInt<N>> {
  pub const ONE: Self = Self(BigInt::<N>::ONE, BigInt::<N>::ZERO);
  pub const ZERO: Self = Self(BigInt::<N>::ZERO, BigInt::<N>::ZERO);

  pub const fn new(lo: &BigInt<N>, hi: &BigInt<N>) -> Self { Self(*lo, *hi) }

  pub const fn from_words(words: [Word; 2 * N]) -> Self {
    let mut a = [0 as Word; N];
    let mut b = [0 as Word; N];

    let mut i = 0;
    while i < N {
      a[i] = words[i];
      i += 1;
    }

    while i < 2 * N {
      b[i - N] = words[i];
      i += 1;
    }

    Self(BigInt(a), BigInt(b))
  }

  pub const fn from_le_bytes(bytes: [u8; N * 2 * BYTES]) -> Self
  where [(); N * BYTES]: {
    let mut a = [0u8; N * BYTES];
    let mut b = [0u8; N * BYTES];

    let mut i = 0;
    while i < N * BYTES {
      a[i] = bytes[i];
      i += 1;
    }

    while i < 2 * N * BYTES {
      b[i - N * BYTES] = bytes[i];
      i += 1;
    }

    Self(BigInt::<N>::from_le_bytes(a), BigInt::<N>::from_le_bytes(b))
  }

  pub const fn gt(&self, rhs: &Self) -> bool {
    if self.1.neq(&rhs.1) {
      return self.1.gt(&rhs.1);
    }
    self.0.gt(&rhs.0)
  }

  pub const fn lt(&self, rhs: &Self) -> bool {
    if self.1.neq(&rhs.1) {
      return self.1.lt(&rhs.1);
    }
    self.0.lt(&rhs.0)
  }

  pub const fn bitwise_and(&self, rhs: &Self) -> Self {
    let r1 = self.0.bitwise_and(&rhs.0);
    let r2 = self.1.bitwise_and(&rhs.1);

    Self(r1, r2)
  }

  pub const fn carrying_add(&self, rhs: &Self, carry: bool) -> (Self, bool) {
    let (r1, c1) = self.0.carrying_add(&rhs.0, carry);
    let (r2, c2) = self.1.carrying_add(&rhs.1, c1);

    (Self(r1, r2), c2)
  }

  pub const fn add(&self, rhs: &Self) -> Self { self.carrying_add(rhs, false).0 }

  pub const fn borrowing_sub(&self, rhs: &Self, borrow: bool) -> (Self, bool) {
    let (r1, c1) = self.0.borrowing_sub(&rhs.0, borrow);
    let (r2, c2) = self.1.borrowing_sub(&rhs.1, c1);

    (Self(r1, r2), c2)
  }

  pub const fn sub(&self, rhs: &Self) -> Self { self.borrowing_sub(rhs, false).0 }

  pub const fn carrying_mul_word(&self, rhs: Word, carry: Word) -> (Self, Word) {
    let (r1, c1) = self.0.carrying_mul_word(rhs, carry);
    let (r2, c2) = self.1.carrying_mul_word(rhs, c1);

    (Self(r1, r2), c2)
  }

  pub const fn mul_word(&self, rhs: Word) -> Self { self.carrying_mul_word(rhs, 0).0 }

  pub const fn mul_half(&self, rhs: &BigInt<N>) -> Self
  where [(); N * 2]: {
    let (r1, c1) = self.0.widening_mul(rhs);
    let (r2, _) = self.1.widening_mul(rhs);

    Self(r1, r2.carrying_add(&c1, false).0)
  }

  pub const fn widening_mul(&self, rhs: &Self) -> (Self, Self)
  where [(); N * 2]: {
    let mut w = [BigInt::<N>::ZERO; 4];
    let x = [self.0, self.1];
    let y = [rhs.0, rhs.1];
    let mut i = 0;
    while i < 2 {
      let mut j = 0;
      let mut carry = BigInt::<N>::ZERO;
      while j < 2 {
        let (r0, c0) = x[j].widening_mul(&y[i]);
        let (r1, c1) = w[i + j].carrying_add(&carry, false);
        let (r2, c2) = r1.carrying_add(&r0, false);
        w[i + j] = r2;
        carry = c0.carrying_add(&BigInt::from_u32(c1 as u32 + c2 as u32), false).0;
        j += 1;
      }
      w[i + 2] = carry;
      i += 1;
    }

    (Self(w[0], w[1]), Self(w[2], w[3]))
  }

  pub const fn shl(&self, shift: u32) -> Self {
    assert!(shift < 2 * N as u32 * Word::BITS);

    if shift < N as u32 * Word::BITS {
      let (r1, c1) = self.0.shl(shift);
      let r2 = self.1.shl(shift).0.bitwise_or(&c1);

      Self(r1, r2)
    } else {
      let shiftr = shift % (N as u32 * Word::BITS);
      let r2 = self.0.shl(shiftr).0;

      Self(BigInt::ZERO, r2)
    }
  }

  pub const fn shr(&self, shift: u32) -> Self {
    assert!(shift < 2 * N as u32 * Word::BITS);

    if shift < N as u32 * Word::BITS {
      let (r2, c2) = self.1.shr(shift);
      let r1 = self.0.shr(shift).0.bitwise_or(&c2);

      Self(r1, r2)
    } else {
      let shiftr = shift % (N as u32 * Word::BITS);
      let r1 = self.1.shr(shiftr).0;

      Self(r1, BigInt::ZERO)
    }
  }

  pub const fn split(self) -> (BigInt<N>, BigInt<N>) { (self.0, self.1) }

  pub const fn to_le_bytes(&self) -> [u8; N * 2 * BYTES]
  where [(); N * BYTES]: {
    let a: [u8; N * BYTES] = self.0.to_le_bytes();
    let b: [u8; N * BYTES] = self.1.to_le_bytes();

    let mut c = [0u8; N * 2 * BYTES];

    let mut i = 0;
    while i < N * BYTES {
      c[i] = a[i];
      i += 1;
    }

    while i < 2 * N * BYTES {
      c[i] = b[i - N * BYTES];
      i += 1;
    }

    c
  }

  pub const fn to_words(self) -> [Word; N * 2]
  where [(); N * 2]: {
    let a = self.0.to_words();
    let b = self.1.to_words();

    let mut c = [0 as Word; N * 2];

    let mut i = 0;
    while i < N {
      c[i] = a[i];
      i += 1;
    }
    while i < 2 * N {
      c[i] = b[i - N];
      i += 1;
    }

    c
  }
}

#[cfg(test)]
mod tests {
  use crypto_bigint::{Encoding, Limb, U256, U512};
  use hex_literal::hex;
  use rand::Rng;

  use super::*;

  #[test]
  fn test_from() {
    let mut rng = rand::thread_rng();
    for _ in 0..100000 {
      let bytes: [u8; 32] =
        (0..32).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let actual1 = BigInt::<4>::from_le_bytes(bytes).0;
      let expected1 = U256::from_le_bytes(bytes).to_words();
      assert_eq!(actual1, expected1);

      let actual2 = BigInt::<4>::from_be_bytes(bytes).0;
      let expected2 = U256::from_be_bytes(bytes).to_words();
      assert_eq!(actual2, expected2);

      let a = rng.gen();
      let expected = U256::from_u32(a).to_words();
      let actual = BigInt::<4>::from_u32(a).0;
      assert_eq!(actual, expected);
    }
  }

  #[test]
  fn test_add_sub() {
    let mut rng = rand::thread_rng();
    for _ in 0..10000 {
      let x_bytes: [u8; 32] =
        (0..32).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let y_bytes: [u8; 32] =
        (0..32).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let x = BigInt::<4>::from_le_bytes(x_bytes);
      let y = BigInt::<4>::from_le_bytes(y_bytes);

      let (z1, c1) = x.carrying_add(&y, false);
      let (z2, c2) = x.borrowing_sub(&y, false);

      let actual1 = z1.to_le_bytes();
      let actual2 = z2.to_le_bytes();
      let actual3 = (c1 as Word).to_le_bytes();
      let actual4 = (c2 as Word).wrapping_neg().to_le_bytes();

      let p = U256::from_le_bytes(x_bytes);
      let q = U256::from_le_bytes(y_bytes);

      let (r1, s1) = p.adc(&q, Limb::ZERO);
      let (r2, s2) = p.sbb(&q, Limb::ZERO);

      let expected1 = r1.to_le_bytes();
      let expected2 = r2.to_le_bytes();
      let expected3 = s1.to_le_bytes();
      let expected4 = s2.to_le_bytes();

      assert_eq!(actual1, expected1);
      assert_eq!(actual2, expected2);
      assert_eq!(actual3, expected3);
      assert_eq!(actual4, expected4);
    }
  }

  #[test]
  fn test_mul() {
    let mut rng = rand::thread_rng();
    for _i in 0..10000 {
      let x_bytes: [u8; 32] =
        (0..32).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let y_bytes: [u8; 32] =
        (0..32).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let x = BigInt::<4>::from_le_bytes(x_bytes);
      let y = BigInt::<4>::from_le_bytes(y_bytes);

      let (z1, c1) = x.widening_mul(&y);

      let p = U256::from_le_bytes(x_bytes);
      let q = U256::from_le_bytes(y_bytes);

      let (r1, s1) = p.widening_mul(&q).split();

      let actual1 = z1.0;
      let actual2 = c1.0;

      let expected1 = r1.to_words();
      let expected2 = s1.to_words();

      assert_eq!(actual1, expected1);
      assert_eq!(actual2, expected2);
    }
  }

  #[test]
  fn test_bitwise() {
    let mut rng = rand::thread_rng();
    for _i in 0..1000 {
      let bytes: [u8; 32] =
        (0..32).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let p = BigInt::<4>::from_le_bytes(bytes);
      let a = U256::from_le_bytes(bytes);

      for shift in 0..=255 {
        let (p1, _) = p.shl(shift);
        let a1 = a.shl(shift);

        let (p2, _) = p.shr(shift);
        let a2 = a.shr(shift);

        let actual1 = p1.to_words();
        let actual2 = p2.to_words();

        let expected1 = a1.to_words();
        let expected2 = a2.to_words();

        assert_eq!(actual1, expected1);
        assert_eq!(actual2, expected2);
      }
    }
  }

  #[test]
  fn test_concat() {
    let mut rng = rand::thread_rng();
    for _i in 0..1000 {
      let bytes: [u8; 64] =
        (0..64).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let u = BigInt::<4>::from_le_bytes(bytes[..32].try_into().unwrap());
      let v = BigInt::<4>::from_le_bytes(bytes[32..].try_into().unwrap());
      let p = Concat::new(&u, &v);
      let a = U512::from_le_bytes(bytes);

      for shift in 0..=511 {
        let p1 = p.shl(shift);
        let p2 = p.shr(shift);

        let a1 = a.shl(shift);
        let a2 = a.shr(shift);

        let actual1 = p1.to_words();
        let actual2 = p2.to_words();

        let expected1 = a1.to_words();
        let expected2 = a2.to_words();

        assert_eq!(actual1, expected1);
        assert_eq!(actual2, expected2);
      }
    }
  }

  #[test]
  fn test_concat_mul() {
    let mut rng = rand::thread_rng();
    for _i in 0..10000 {
      let x_bytes: [u8; 64] =
        (0..64).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let y_bytes: [u8; 64] =
        (0..64).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let mut z_bytes = [0; 64];
      z_bytes[..32].copy_from_slice(&y_bytes[..32]);

      let p = Concat::from_le_bytes(x_bytes);
      let q = Concat::from_le_bytes(y_bytes);
      let r = BigInt::<4>::from_le_bytes(z_bytes[..32].try_into().unwrap());

      let (s0, s1) = p.widening_mul(&q);
      let t = p.mul_half(&r);

      let a = U512::from_le_bytes(x_bytes);
      let b = U512::from_le_bytes(y_bytes);
      let c = U512::from_le_bytes(z_bytes);

      let (c0, c1) = a.widening_mul(&b).split();
      let (d0, _d1) = a.widening_mul(&c).split();

      let actual1 = s0.to_words();
      let actual2 = s1.to_words();
      let actual3 = t.to_words();

      let expected1 = c0.to_words();
      let expected2 = c1.to_words();
      let expected3 = d0.to_words();

      assert_eq!(actual1, expected1);
      assert_eq!(actual2, expected2);
      assert_eq!(actual3, expected3);
    }
  }

  #[test]
  fn test_concat_ops() {
    let mut rng = rand::thread_rng();
    for _i in 0..10000 {
      let mut x_bytes: [u8; 64] =
        (0..64).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      let mut y_bytes: [u8; 64] =
        (0..64).map(|_| rng.gen_range(0..=255)).collect::<Vec<_>>().try_into().unwrap();

      x_bytes[63] = 128;
      y_bytes[63] = 64;

      let p = Concat::<BigInt<4>>::from_le_bytes(x_bytes);
      let q = Concat::<BigInt<4>>::from_le_bytes(y_bytes);

      let r1 = p.sub(&q);
      let r2 = p.add(&q);

      let a = U512::from_le_bytes(x_bytes);
      let b = U512::from_le_bytes(y_bytes);

      let c1 = a - b;
      let c2 = a + b;

      let actual1 = r1.to_words();
      let actual2 = r2.to_words();

      let expected1 = c1.to_words();
      let expected2 = c2.to_words();

      assert_eq!(actual1, expected1);
      assert_eq!(actual2, expected2);
    }
  }

  #[test]
  fn test_mu() {
    let mu = calculate_mu(&BigInt::<4>::from_be_bytes(hex!(
      "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"
    )));

    let actual = mu.to_le_bytes();
    let expected = [
      0x1B, 0x13, 0x2C, 0x0A, 0xA3, 0xE5, 0x9C, 0xED, 0xA7, 0x29, 0x63, 0x08, 0x5D, 0x21, 0x06,
      0x21, 0xEB, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
      0xFF, 0xFF, 0x0F, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0,
    ];

    assert_eq!(actual, expected);
  }
}
