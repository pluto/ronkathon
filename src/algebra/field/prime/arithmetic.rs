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
  use rstest::rstest;

  use super::*;

  #[rstest]
  #[case(PlutoScalarField::new(0), PlutoScalarField::new(0), PlutoScalarField::new(0))]
  #[case(PlutoScalarField::new(1), PlutoScalarField::new(1), PlutoScalarField::new(2))]
  #[case(PlutoScalarField::new(12), PlutoScalarField::new(5), PlutoScalarField::new(0))]
  #[case(PlutoScalarField::new(5), PlutoScalarField::new(12), PlutoScalarField::new(0))]
  #[case(PlutoScalarField::new(10), PlutoScalarField::new(10), PlutoScalarField::new(3))]
  #[case(PlutoBaseField::new(0), PlutoBaseField::new(0), PlutoBaseField::new(0))]
  #[case(PlutoBaseField::new(1), PlutoBaseField::new(1), PlutoBaseField::new(2))]
  #[case(PlutoBaseField::new(40), PlutoBaseField::new(61), PlutoBaseField::new(0))]
  #[case(PlutoBaseField::new(61), PlutoBaseField::new(40), PlutoBaseField::new(0))]
  #[case(PlutoBaseField::new(60), PlutoBaseField::new(60), PlutoBaseField::new(19))]
  fn add<const P: usize>(
    #[case] a: PrimeField<P>,
    #[case] b: PrimeField<P>,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a + b, expected);
  }

  #[rstest]
  #[case(PlutoScalarField::new(0), PlutoScalarField::new(0), PlutoScalarField::new(0))]
  #[case(PlutoScalarField::new(1), PlutoScalarField::new(1), PlutoScalarField::new(0))]
  #[case(PlutoScalarField::new(12), PlutoScalarField::new(5), PlutoScalarField::new(7))]
  #[case(PlutoScalarField::new(5), PlutoScalarField::new(12), PlutoScalarField::new(10))]
  #[case(PlutoScalarField::new(10), PlutoScalarField::new(17), PlutoScalarField::new(10))]
  #[case(PlutoBaseField::new(0), PlutoBaseField::new(0), PlutoBaseField::new(0))]
  #[case(PlutoBaseField::new(1), PlutoBaseField::new(1), PlutoBaseField::new(0))]
  #[case(PlutoBaseField::new(40), PlutoBaseField::new(61), PlutoBaseField::new(80))]
  #[case(PlutoBaseField::new(61), PlutoBaseField::new(40), PlutoBaseField::new(21))]
  #[case(PlutoBaseField::new(60), PlutoBaseField::new(60), PlutoBaseField::new(0))]
  fn sub<const P: usize>(
    #[case] a: PrimeField<P>,
    #[case] b: PrimeField<P>,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a - b, expected);
  }

  #[rstest]
  #[case(PlutoScalarField::new(0), PlutoScalarField::new(0), PlutoScalarField::new(0))]
  #[case(PlutoScalarField::new(1), PlutoScalarField::new(1), PlutoScalarField::new(1))]
  #[case(PlutoScalarField::new(12), PlutoScalarField::new(5), PlutoScalarField::new(9))]
  #[case(PlutoScalarField::new(5), PlutoScalarField::new(12), PlutoScalarField::new(9))]
  #[case(PlutoScalarField::new(10), PlutoScalarField::new(10), PlutoScalarField::new(15))]
  #[case(PlutoBaseField::new(0), PlutoBaseField::new(0), PlutoBaseField::new(0))]
  #[case(PlutoBaseField::new(1), PlutoBaseField::new(1), PlutoBaseField::new(1))]
  #[case(PlutoBaseField::new(40), PlutoBaseField::new(61), PlutoBaseField::new(16))]
  #[case(PlutoBaseField::new(61), PlutoBaseField::new(40), PlutoBaseField::new(16))]
  #[case(PlutoBaseField::new(60), PlutoBaseField::new(60), PlutoBaseField::new(65))]
  fn mul<const P: usize>(
    #[case] a: PrimeField<P>,
    #[case] b: PrimeField<P>,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a * b, expected);
  }

  fn combined_arithmetic_check<const P: usize>() {
    let mut rng = rand::thread_rng();
    let x = rng.gen::<PrimeField<P>>();
    let y = rng.gen::<PrimeField<P>>();
    let z = rng.gen::<PrimeField<P>>();
    assert_eq!(x + (-x), <PrimeField<P>>::ZERO);
    assert_eq!(-x, <PrimeField<P>>::ZERO - x);
    assert_eq!(x + x, x * <PrimeField<P>>::new(2));
    assert_eq!(x, x.div(<PrimeField<P>>::new(2)) * <PrimeField<P>>::new(2));
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
  #[case(PlutoScalarField::new(0), 0, PlutoScalarField::new(1))]
  #[case(PlutoScalarField::new(0), 10, PlutoScalarField::new(0))]
  #[case(PlutoScalarField::new(12), 5, PlutoScalarField::new(3))]
  #[case(PlutoScalarField::new(5), 12, PlutoScalarField::new(4))]
  #[case(PlutoScalarField::new(10), 10, PlutoScalarField::new(2))]
  #[case(PlutoBaseField::new(0), 0, PlutoBaseField::new(1))]
  #[case(PlutoBaseField::new(0), 10, PlutoBaseField::new(0))]
  #[case(PlutoBaseField::new(40), 5, PlutoBaseField::new(39))]
  #[case(PlutoBaseField::new(61), 3, PlutoBaseField::new(34))]
  #[case(PlutoBaseField::new(25), 25, PlutoBaseField::new(1))]
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
  #[case(PlutoScalarField::new(0), PlutoScalarField::new(69420))]
  #[case(PlutoScalarField::new(1), PlutoScalarField::new(1))]
  #[case(PlutoScalarField::new(12), PlutoScalarField::new(10))]
  #[case(PlutoScalarField::new(5), PlutoScalarField::new(7))]
  #[case(PlutoScalarField::new(10), PlutoScalarField::new(12))]
  // First case will panic here so the "expected" value is not relevant.
  #[should_panic]
  #[case(PlutoBaseField::new(0), PlutoBaseField::new(69420))]
  #[case(PlutoBaseField::new(1), PlutoBaseField::new(1))]
  #[case(PlutoBaseField::new(15), PlutoBaseField::new(27))]
  #[case(PlutoBaseField::new(61), PlutoBaseField::new(53))]
  #[case(PlutoBaseField::new(25), PlutoBaseField::new(97))]
  fn multiplicative_inverse<const P: usize>(
    #[case] a: PrimeField<P>,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a.inverse().unwrap(), expected);
    assert_eq!(a.inverse().unwrap() * a, PrimeField::<P>::ONE);
  }

  #[rstest]
  #[case(PlutoScalarField::new(0), PlutoScalarField::new(0))]
  #[case(PlutoScalarField::new(10), PlutoScalarField::new(5))]
  #[case(PlutoScalarField::new(12), PlutoScalarField::new(6))]
  #[case(PlutoScalarField::new(1), PlutoScalarField::new(9))]
  #[case(PlutoScalarField::new(3), PlutoScalarField::new(10))]
  #[case(PlutoBaseField::new(0), PlutoBaseField::new(0))]
  #[case(PlutoBaseField::new(1), PlutoBaseField::new(51))]
  #[case(PlutoBaseField::new(15), PlutoBaseField::new(58))]
  #[case(PlutoBaseField::new(61), PlutoBaseField::new(81))]
  #[case(PlutoBaseField::new(25), PlutoBaseField::new(63))]
  fn halve<const P: usize>(#[case] a: PrimeField<P>, #[case] expected: PrimeField<P>) {
    assert_eq!(a / PrimeField::<P>::new(2), expected);
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
