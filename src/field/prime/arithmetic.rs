use super::*;

impl<const P: usize> Add for PrimeField<P> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self { Self { value: (self.value + rhs.value) % Self::ORDER } }
}

impl<const P: usize> AddAssign for PrimeField<P> {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<const P: usize> Sum for PrimeField<P> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO)
  }
}

impl<const P: usize> Sub for PrimeField<P> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let (mut diff, over) = self.value.overflowing_sub(rhs.value);
    let corr = if over { Self::ORDER } else { 0 };
    diff = diff.wrapping_add(corr);
    Self { value: diff }
  }
}

impl<const P: usize> SubAssign for PrimeField<P> {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<const P: usize> Mul for PrimeField<P> {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self { Self { value: (self.value * rhs.value) % Self::ORDER } }
}

impl<const P: usize> MulAssign for PrimeField<P> {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<const P: usize> Product for PrimeField<P> {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl<const P: usize> Div for PrimeField<P> {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self { self * rhs.inverse().unwrap() }
}

impl<const P: usize> DivAssign for PrimeField<P> {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl<const P: usize> Neg for PrimeField<P> {
  type Output = Self;

  fn neg(self) -> Self::Output { Self::ZERO - self }
}

impl<const P: usize> Rem for PrimeField<P> {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self { self - (self / rhs) * rhs }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[rstest]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(1), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(1), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(2))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(12), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(5), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(5), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(12), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(10), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(10), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(3))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(0), PrimeField::<{ PlutoPrime::Base as usize }>::new(0), PrimeField::<{ PlutoPrime::Base as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(1), PrimeField::<{ PlutoPrime::Base as usize }>::new(1), PrimeField::<{ PlutoPrime::Base as usize }>::new(2))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(40), PrimeField::<{ PlutoPrime::Base as usize }>::new(61), PrimeField::<{ PlutoPrime::Base as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(61), PrimeField::<{ PlutoPrime::Base as usize }>::new(40), PrimeField::<{ PlutoPrime::Base as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(60), PrimeField::<{ PlutoPrime::Base as usize }>::new(60), PrimeField::<{ PlutoPrime::Base as usize }>::new(19))]
  fn add<const P: usize>(
    #[case] a: PrimeField<P>,
    #[case] b: PrimeField<P>,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a + b, expected);
  }

  #[rstest]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(1), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(1), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(12), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(5), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(7))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(5), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(12), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(10))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(10), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(17), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(10))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(0), PrimeField::<{ PlutoPrime::Base as usize }>::new(0), PrimeField::<{ PlutoPrime::Base as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(1), PrimeField::<{ PlutoPrime::Base as usize }>::new(1), PrimeField::<{ PlutoPrime::Base as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(40), PrimeField::<{ PlutoPrime::Base as usize }>::new(61), PrimeField::<{ PlutoPrime::Base as usize }>::new(80))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(61), PrimeField::<{ PlutoPrime::Base as usize }>::new(40), PrimeField::<{ PlutoPrime::Base as usize }>::new(21))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(60), PrimeField::<{ PlutoPrime::Base as usize }>::new(60), PrimeField::<{ PlutoPrime::Base as usize }>::new(0))]
  fn sub<const P: usize>(
    #[case] a: PrimeField<P>,
    #[case] b: PrimeField<P>,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a - b, expected);
  }

  #[rstest]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(1), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(1), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(1))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(12), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(5), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(9))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(5), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(12), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(9))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(10), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(10), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(15))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(0), PrimeField::<{ PlutoPrime::Base as usize }>::new(0), PrimeField::<{ PlutoPrime::Base as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(1), PrimeField::<{ PlutoPrime::Base as usize }>::new(1), PrimeField::<{ PlutoPrime::Base as usize }>::new(1))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(40), PrimeField::<{ PlutoPrime::Base as usize }>::new(61), PrimeField::<{ PlutoPrime::Base as usize }>::new(16))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(61), PrimeField::<{ PlutoPrime::Base as usize }>::new(40), PrimeField::<{ PlutoPrime::Base as usize }>::new(16))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(60), PrimeField::<{ PlutoPrime::Base as usize }>::new(60), PrimeField::<{ PlutoPrime::Base as usize }>::new(65))]
  fn mul<const P: usize>(
    #[case] a: PrimeField<P>,
    #[case] b: PrimeField<P>,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a * b, expected);
  }

  fn combined_arithmetic_check<const P: usize>() {
    let mut rng = rand::thread_rng();
    // for i in 0..1000 {
    let x = rng.gen::<PrimeField<P>>();
    let y = rng.gen::<PrimeField<P>>();
    let z = rng.gen::<PrimeField<P>>();
    assert_eq!(x + (-x), <PrimeField<P>>::ZERO);
    assert_eq!(-x, <PrimeField<P>>::ZERO - x);
    assert_eq!(x + x, x * <PrimeField<P>>::TWO);
    assert_eq!(x, x.div(<PrimeField<P>>::TWO) * <PrimeField<P>>::TWO);
    assert_eq!(x * (-x), -(x * x));
    assert_eq!(x * y, y * x);
    assert_eq!(x * (y * z), (x * y) * z);
    assert_eq!(x - (y + z), (x - y) - z);
    assert_eq!((x + y) - z, x + (y - z));
    assert_eq!(x * (y + z), x * y + x * z);
    assert_eq!(x + y + z + x + y + z, [x, x, y, y, z, z].iter().cloned().sum());
  }

  #[rstest]
  #[case(PlutoPrime::Base)]
  #[case(PlutoPrime::Scalar)]
  fn add_sub_neg_mul(#[case] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => combined_arithmetic_check::<{ PlutoPrime::Base as usize }>(),
      PlutoPrime::Scalar => combined_arithmetic_check::<{ PlutoPrime::Scalar as usize }>(),
    }
  }

  #[rstest]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0), 0, PrimeField::<{ PlutoPrime::Scalar as usize }>::new(1))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0), 10, PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(12), 5, PrimeField::<{ PlutoPrime::Scalar as usize }>::new(3))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(5), 12, PrimeField::<{ PlutoPrime::Scalar as usize }>::new(4))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(10), 10, PrimeField::<{ PlutoPrime::Scalar as usize }>::new(2))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(0), 0, PrimeField::<{ PlutoPrime::Base as usize }>::new(1))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(0), 10, PrimeField::<{ PlutoPrime::Base as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(40), 5, PrimeField::<{ PlutoPrime::Base as usize }>::new(39))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(61), 3, PrimeField::<{ PlutoPrime::Base as usize }>::new(34))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(25), 25, PrimeField::<{ PlutoPrime::Base as usize }>::new(1))]
  fn field_pow<const P: usize>(
    #[case] a: PrimeField<P>,
    #[case] pow: usize,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a.pow(pow), expected);
  }

  #[rstest]
  // First case will panic here so the "expected" value is not relevant.
  #[should_panic]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(69420))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(1), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(1))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(12), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(10))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(5), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(7))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(10), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(12))]
  // First case will panic here so the "expected" value is not relevant.
  #[should_panic]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(0),  PrimeField::<{ PlutoPrime::Base as usize }>::new(69420))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(1),  PrimeField::<{ PlutoPrime::Base as usize }>::new(1))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(15), PrimeField::<{ PlutoPrime::Base as usize }>::new(27))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(61), PrimeField::<{ PlutoPrime::Base as usize }>::new(53))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(25), PrimeField::<{ PlutoPrime::Base as usize }>::new(97))]
  fn multiplicative_inverse<const P: usize>(
    #[case] a: PrimeField<P>,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a.inverse().unwrap(), expected);
    assert_eq!(a.inverse().unwrap() * a, PrimeField::<P>::ONE);
  }

  #[rstest]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(10), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(5))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(12), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(6))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(1), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(9))]
  #[case(PrimeField::<{ PlutoPrime::Scalar as usize }>::new(3), PrimeField::<{ PlutoPrime::Scalar as usize }>::new(10))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(0),  PrimeField::<{ PlutoPrime::Base as usize }>::new(0))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(1),  PrimeField::<{ PlutoPrime::Base as usize }>::new(51))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(15), PrimeField::<{ PlutoPrime::Base as usize }>::new(58))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(61), PrimeField::<{ PlutoPrime::Base as usize }>::new(81))]
  #[case(PrimeField::<{ PlutoPrime::Base as usize }>::new(25), PrimeField::<{ PlutoPrime::Base as usize }>::new(63))]
  fn halve<const P: usize>(#[case] a: PrimeField<P>, #[case] expected: PrimeField<P>) {
    assert_eq!(a / PrimeField::<P>::TWO, expected);
  }

  fn negation_check<const P: usize>() {
    for i in 0..PrimeField::<P>::ORDER {
      let a = PrimeField::<P>::new(i);
      let neg_a = -a;
      assert_eq!(a + neg_a, PrimeField::<P>::ZERO);
    }
  }

  #[rstest]
  #[case(PlutoPrime::Base)]
  #[case(PlutoPrime::Scalar)]
  fn negation(#[case] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => negation_check::<{ PlutoPrime::Base as usize }>(),
      PlutoPrime::Scalar => negation_check::<{ PlutoPrime::Scalar as usize }>(),
    }
  }
  fn distributivity_check<const P: usize>() {
    let a = PrimeField::<P>::new(5);
    let b = PrimeField::<P>::new(6);
    let c = PrimeField::<P>::new(7);
    assert_eq!((a * (b + c)).value, (a * b + a * c).value);
  }

  #[rstest]
  #[case(PlutoPrime::Base)]
  #[case(PlutoPrime::Scalar)]
  fn distributivity(#[case] prime: PlutoPrime) {
    match prime {
      PlutoPrime::Base => distributivity_check::<{ PlutoPrime::Base as usize }>(),
      PlutoPrime::Scalar => distributivity_check::<{ PlutoPrime::Scalar as usize }>(),
    }
  }
}
