use super::*;

mod arithmetic;

pub enum PlutoPrime {
  Base = BASE_FIELD_ORDER as isize,
  Scalar = SCALAR_FIELD_ORDER as isize,
}

pub const BASE_FIELD_ORDER: u32 = 101;
pub const SCALAR_FIELD_ORDER: u32 = 17;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Default)]
pub struct PrimeField<const P: u32> {
  value: u32,
}

impl<const P: u32> PrimeField<P> {
  pub const fn new(value: u32) -> Self {
    is_prime(P);
    Self { value: value % P }
  }
}

impl<const P: u32> const FiniteField for PrimeField<P> {
  const GENERATOR: Self = if P == 2 { Self::ONE } else { find_generator::<P>() };
  const NEG_ONE: Self = Self { value: P - 1 };
  const ONE: Self = Self { value: 1 };
  const ORDER: u32 = P;
  const THREE: Self = Self { value: 3 };
  const TWO: Self = Self { value: 2 };
  const ZERO: Self = Self { value: 0 };

  fn inverse(&self) -> Option<Self> {
    if self.value == 0 {
      return None;
    }
    let exponent = Self::ORDER - 2;
    let mut result = Self::ONE;
    let mut base = *self;
    let mut power = exponent;

    while power > 0 {
      if power & 1 == 1 {
        result *= base;
      }
      base = base * base;
      power >>= 1;
    }
    Some(result)
  }

  fn pow(self, power: u32) -> Self {
    if power == 0 {
      Self::ONE
    } else if power == 1 {
      self
    } else if power % 2 == 0 {
      Self::new((self.pow(power / 2).value * self.pow(power / 2).value) % Self::ORDER)
    } else {
      Self::new((self.pow(power / 2).value * self.pow(power / 2).value * self.value) % Self::ORDER)
    }
  }
}

const fn is_prime(n: u32) {
  let mut i = 2;
  while i * i <= n {
    if n % i == 0 {
      panic!("input is not a prime number");
    }
    i += 1;
  }
}

const fn find_generator<const P: u32>() -> PrimeField<P> {
  let mut i = 2;
  while i * i <= P {
    if (P - 1) % i == 0 {
      if PrimeField::<P>::new(i).pow((P - 1) / i).value != PrimeField::<P>::ONE.value {
        return PrimeField::<P>::new(i);
      } else if PrimeField::<P>::new(P + 1 - i).pow(i).value != PrimeField::<P>::ONE.value {
        return PrimeField::<P>::new(P + 1 - i);
      }
    }
    i += 1;
  }
  panic!("generator not found");
}

impl<const P: u32> Distribution<PrimeField<P>> for Standard {
  #[inline]
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> PrimeField<P> {
    loop {
      let next_u31 = rng.next_u32() >> 4;
      let is_canonical = next_u31 < PrimeField::<P>::ORDER;
      if is_canonical {
        return PrimeField::<P> { value: next_u31 };
      }
    }
  }
}

impl<const P: u32> From<u32> for PrimeField<P> {
  fn from(val: u32) -> Self { Self::new(val) }
}

impl<const P: u32> From<u64> for PrimeField<P> {
  fn from(val: u64) -> Self { Self::new(val as u32) }
}

impl<const P: u32> From<usize> for PrimeField<P> {
  fn from(val: usize) -> Self { Self::new(val as u32) }
}

impl From<PlutoPrime> for u32 {
  fn from(prime: PlutoPrime) -> u32 {
    match prime {
      res @ PlutoPrime::Base => res as u32,
      res @ PlutoPrime::Scalar => res as u32,
    }
  }
}

#[cfg(test)]
mod tests {

  use super::*;

  #[rstest]
  #[case(PlutoPrime::Base)]
  #[case(PlutoPrime::Scalar)]
  fn prime_field(#[case] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => {
        PrimeField::<BASE_FIELD_ORDER>::new(0);
      },
      PlutoPrime::Scalar => {
        PrimeField::<SCALAR_FIELD_ORDER>::new(0);
      },
    };
  }

  #[test]
  #[should_panic]
  fn non_prime_is_not_finite_field() { let _ = PrimeField::<100>::new(0); }

  fn generator_check<const P: u32>() {
    let g = PrimeField::<P>::GENERATOR;
    let mut counter = 1;
    let mut val = g;
    while val != PrimeField::<P>::ONE {
      val *= g;
      counter += 1;
    }
    assert_eq!(counter, P - 1);
  }

  #[rstest]
  fn generator(#[values(PlutoPrime::Base, PlutoPrime::Scalar)] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => generator_check::<BASE_FIELD_ORDER>(),
      PlutoPrime::Scalar => generator_check::<SCALAR_FIELD_ORDER>(),
    }
  }

  fn zero_check<const P: u32>() {
    assert_eq!(PrimeField::<P>::new(0).value, 0);
    assert_eq!(PrimeField::<P>::new(P).value, 0);
  }

  #[rstest]
  #[case(PlutoPrime::Base)]
  #[case(PlutoPrime::Scalar)]
  fn zero(#[case] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => zero_check::<BASE_FIELD_ORDER>(),
      PlutoPrime::Scalar => zero_check::<SCALAR_FIELD_ORDER>(),
    }
  }

  fn non_zero_check<const P: u32>() {
    let a = PrimeField::<P>::new(10);
    assert!(!(a == PrimeField::<P>::ZERO));
  }

  #[rstest]
  #[case(PlutoPrime::Base)]
  #[case(PlutoPrime::Scalar)]
  fn non_zero(#[case] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => non_zero_check::<BASE_FIELD_ORDER>(),
      PlutoPrime::Scalar => non_zero_check::<SCALAR_FIELD_ORDER>(),
    }
  }

  fn identity_elements_check<const P: u32>() {
    let zero = PrimeField::<P>::new(0);
    let one = PrimeField::<P>::new(1);
    for i in 0..PrimeField::<P>::ORDER {
      let f = PrimeField::<P>::new(i);
      assert_eq!(f + zero, f);
      assert_eq!(f * one, f);
      assert_eq!(f * zero, zero);
    }
  }

  #[rstest]
  #[case(PlutoPrime::Base)]
  #[case(PlutoPrime::Scalar)]
  fn identity_elements(#[case] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => identity_elements_check::<BASE_FIELD_ORDER>(),
      PlutoPrime::Scalar => identity_elements_check::<SCALAR_FIELD_ORDER>(),
    }
  }

  #[rstest]
  #[should_panic]
  // First case will panic here so the "expected" value is not relevant.
  #[case(PrimeField::<17>::new(0), PrimeField::<17>::new(69420))]
  #[case(PrimeField::<17>::new(1), PrimeField::<17>::new(1))]
  #[case(PrimeField::<17>::new(12), PrimeField::<17>::new(10))]
  #[case(PrimeField::<17>::new(5), PrimeField::<17>::new(7))]
  #[case(PrimeField::<17>::new(10), PrimeField::<17>::new(12))]
  fn multiplicative_inverse<const P: u32>(
    #[case] a: PrimeField<P>,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a.inverse().unwrap(), expected);
    assert_eq!(a.inverse().unwrap() * a, PrimeField::<P>::ONE);
  }

  fn inverse_of_inverse_check<const P: u32>() {
    for i in 1..PrimeField::<P>::ORDER {
      let a = PrimeField::<P>::new(i);
      let a_inv = a.inverse().unwrap();
      let a_inv_inv = a_inv.inverse().unwrap();
      assert_eq!(a_inv_inv, a);
    }
  }

  #[rstest]
  #[case(PlutoPrime::Base)]
  #[case(PlutoPrime::Scalar)]
  fn inverse_of_inverse(#[case] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => inverse_of_inverse_check::<BASE_FIELD_ORDER>(),
      PlutoPrime::Scalar => inverse_of_inverse_check::<SCALAR_FIELD_ORDER>(),
    }
  }

  #[should_panic]
  #[test]
  fn not_primitive_root_of_unity() {
    let n = 3;
    let _root = PrimeField::<17>::primitive_root_of_unity(n);
  }
}
