use super::*;

impl<const P: u32> Add for PrimeField<P> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self { Self { value: (self.value + rhs.value) % Self::ORDER } }
}

impl<const P: u32> AddAssign for PrimeField<P> {
  fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<const P: u32> Sum for PrimeField<P> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO)
  }
}

impl<const P: u32> Sub for PrimeField<P> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let (mut diff, over) = self.value.overflowing_sub(rhs.value);
    let corr = if over { Self::ORDER } else { 0 };
    diff = diff.wrapping_add(corr);
    Self { value: diff }
  }
}

impl<const P: u32> SubAssign for PrimeField<P> {
  fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<const P: u32> Mul for PrimeField<P> {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self { Self { value: (self.value * rhs.value) % Self::ORDER } }
}

impl<const P: u32> MulAssign for PrimeField<P> {
  fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<const P: u32> Product for PrimeField<P> {
  fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
    iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
  }
}

impl<const P: u32> Div for PrimeField<P> {
  type Output = Self;

  #[allow(clippy::suspicious_arithmetic_impl)]
  fn div(self, rhs: Self) -> Self { self * rhs.inverse().unwrap() }
}

impl<const P: u32> DivAssign for PrimeField<P> {
  fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl<const P: u32> Neg for PrimeField<P> {
  type Output = Self;

  fn neg(self) -> Self::Output { Self::ZERO - self }
}

impl<const P: u32> Rem for PrimeField<P> {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self { self - (self / rhs) * rhs }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[rstest]
  #[case(PrimeField::<17>::new(0), PrimeField::<17>::new(0), PrimeField::<17>::new(0))]
  #[case(PrimeField::<17>::new(1), PrimeField::<17>::new(1), PrimeField::<17>::new(2))]
  #[case(PrimeField::<17>::new(12), PrimeField::<17>::new(5), PrimeField::<17>::new(0))]
  #[case(PrimeField::<17>::new(5), PrimeField::<17>::new(12), PrimeField::<17>::new(0))]
  #[case(PrimeField::<17>::new(10), PrimeField::<17>::new(10), PrimeField::<17>::new(3))]
  fn add<const P: u32>(
    #[case] a: PrimeField<P>,
    #[case] b: PrimeField<P>,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a + b, expected);
  }

  #[rstest]
  #[case(PrimeField::<17>::new(0), PrimeField::<17>::new(0), PrimeField::<17>::new(0))]
  #[case(PrimeField::<17>::new(1), PrimeField::<17>::new(1), PrimeField::<17>::new(0))]
  #[case(PrimeField::<17>::new(12), PrimeField::<17>::new(5), PrimeField::<17>::new(7))]
  #[case(PrimeField::<17>::new(5), PrimeField::<17>::new(12), PrimeField::<17>::new(10))]
  #[case(PrimeField::<17>::new(10), PrimeField::<17>::new(17), PrimeField::<17>::new(10))]
  fn sub<const P: u32>(
    #[case] a: PrimeField<P>,
    #[case] b: PrimeField<P>,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a - b, expected);
  }

  #[rstest]
  #[case(PrimeField::<17>::new(0), PrimeField::<17>::new(0), PrimeField::<17>::new(0))]
  #[case(PrimeField::<17>::new(1), PrimeField::<17>::new(1), PrimeField::<17>::new(1))]
  #[case(PrimeField::<17>::new(12), PrimeField::<17>::new(5), PrimeField::<17>::new(9))]
  #[case(PrimeField::<17>::new(5), PrimeField::<17>::new(12), PrimeField::<17>::new(9))]
  #[case(PrimeField::<17>::new(10), PrimeField::<17>::new(10), PrimeField::<17>::new(15))]
  fn mul<const P: u32>(
    #[case] a: PrimeField<P>,
    #[case] b: PrimeField<P>,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a * b, expected);
  }

  fn combined_arithmetic_check<const P: u32>() {
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
      PlutoPrime::Base => combined_arithmetic_check::<BASE_FIELD_ORDER>(),
      PlutoPrime::Scalar => combined_arithmetic_check::<SCALAR_FIELD_ORDER>(),
    }
  }

  #[rstest]
  #[case(PrimeField::<17>::new(0), 0, PrimeField::<17>::new(1))]
  #[case(PrimeField::<17>::new(0), 10, PrimeField::<17>::new(0))]
  #[case(PrimeField::<17>::new(12), 5, PrimeField::<17>::new(3))]
  #[case(PrimeField::<17>::new(5), 12, PrimeField::<17>::new(4))]
  #[case(PrimeField::<17>::new(10), 10, PrimeField::<17>::new(2))]
  fn field_pow<const P: u32>(
    #[case] a: PrimeField<P>,
    #[case] pow: u64,
    #[case] expected: PrimeField<P>,
  ) {
    assert_eq!(a.pow(pow), expected);
  }

  #[rstest]
  #[case(PrimeField::<17>::new(0), PrimeField::<17>::new(0))]
  #[case(PrimeField::<17>::new(10), PrimeField::<17>::new(5))]
  #[case(PrimeField::<17>::new(12), PrimeField::<17>::new(6))]
  #[case(PrimeField::<17>::new(1), PrimeField::<17>::new(9))]
  #[case(PrimeField::<17>::new(3), PrimeField::<17>::new(10))]
  fn halve<const P: u32>(#[case] a: PrimeField<P>, #[case] expected: PrimeField<P>) {
    assert_eq!(a / PrimeField::<P>::TWO, expected);
  }

  fn negation_check<const P: u32>() {
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
      PlutoPrime::Base => negation_check::<BASE_FIELD_ORDER>(),
      PlutoPrime::Scalar => negation_check::<SCALAR_FIELD_ORDER>(),
    }
  }
  fn distributivity_check<const P: u32>() {
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
      PlutoPrime::Base => distributivity_check::<BASE_FIELD_ORDER>(),
      PlutoPrime::Scalar => distributivity_check::<SCALAR_FIELD_ORDER>(),
    }
  }
}
