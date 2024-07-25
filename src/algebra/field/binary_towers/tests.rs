use rand::{thread_rng, Rng};
use rstest::rstest;

use super::*;
use crate::PrimeField;

type TestBinaryField = PrimeField<2>;

pub(super) fn num_digits(n: u64) -> usize {
  let r = format!("{:b}", n);
  r.len()
}

fn from_bool_vec(num: Vec<BinaryField>) -> u64 {
  let mut result: u64 = 0;
  for (i, &bit) in num.iter().rev().enumerate() {
    if bit == BinaryField::One {
      result |= 1 << (num.len() - 1 - i);
    }
  }
  result
}

#[rstest]
#[case(0, 1)]
#[case(1, 1)]
#[should_panic]
#[case(1, 0)]
fn binary_field_arithmetic(#[case] a: usize, #[case] b: usize) {
  let arg1 = BinaryField::from(a);
  let arg2 = BinaryField::from(b);
  let a_test = TestBinaryField::new(a);
  let b_test = TestBinaryField::new(b);

  assert_eq!((arg1 + arg2), BinaryField::from((a_test + b_test).value));
  assert_eq!(arg1 - arg2, arg1 + arg2);
  assert_eq!((arg1 * arg2), BinaryField::from((a_test * b_test).value));

  let inv_res = arg2.inverse();
  assert!(inv_res.is_some());
  assert_eq!(inv_res.unwrap(), arg2);

  assert_eq!((arg1 / arg2), BinaryField::from((a_test / b_test).value));
}

#[rstest]
#[case(4, 3)]
#[case(9, 4)]
#[case(33, 6)]
#[case(67, 7)]
fn num_digit(#[case] num: u64, #[case] digits: usize) {
  assert_eq!(num_digits(num), digits);
}

#[test]
fn add_sub_neg() {
  let mut rng = thread_rng();
  let a = rng.gen::<BinaryTowers<3>>();
  let b = rng.gen::<BinaryTowers<3>>();

  assert_eq!(a + a, BinaryTowers::<3>::ZERO);
  assert_eq!(a + a, b + b);
  assert_eq!(a + b, b + a);
  assert_eq!(a + b, a - b);
  assert_eq!(a, -a);
  assert_eq!(a + (-b), (-a) + b);
}

#[rstest]
#[case(BinaryTowers::<3>::from(160), BinaryTowers::<3>::from(23), BinaryTowers::<3>::from(90))]
#[case(BinaryTowers::<3>::from(217), BinaryTowers::<3>::from(20), BinaryTowers::<3>::from(151))]
#[case(BinaryTowers::<3>::from(19), BinaryTowers::<3>::from(230), BinaryTowers::<3>::from(3))]
#[case(BinaryTowers::<3>::from(203), BinaryTowers::<3>::from(187), BinaryTowers::<3>::from(4))]
#[case(BinaryTowers::<3>::from(145), BinaryTowers::<3>::from(38), BinaryTowers::<3>::from(152))]
#[case(BinaryTowers::<3>::from(209), BinaryTowers::<3>::from(155), BinaryTowers::<3>::from(71))]
fn mul_div(#[case] a: BinaryTowers<3>, #[case] b: BinaryTowers<3>, #[case] res: BinaryTowers<3>) {
  let c = a * b;
  assert_eq!(a * b, res);
  assert_eq!(b * a, res);

  let d = a / b;
  assert_eq!(d * c, a.pow(2));

  let e = BinaryTowers::<3>::ONE / (a * b);
  assert_eq!(a * b * e, BinaryTowers::<3>::ONE);
}

#[test]
fn small_by_large_mul() {
  let mut rng = thread_rng();
  for _ in 0..100 {
    let a = rng.gen::<BinaryTowers<5>>();

    let val = rng.gen_range(0..1 << (1 << 3));

    let b = BinaryTowers::<3>::from(val);
    let d = BinaryTowers::<5>::from(val);

    let small_by_large_res = a * b;
    let res = from_bool_vec(small_by_large_res.coefficients.to_vec());

    let mul_res = a * d;
    let res_2 = from_bool_vec(mul_res.coefficients.to_vec());

    assert_eq!(res, res_2);

    // return self if second operand's extension field > first operand
    assert_eq!(b, b * a);
  }
}

#[test]
fn efficient_embedding() {
  let mut rng = thread_rng();
  let a = rng.gen::<BinaryTowers<4>>();

  let (a1, a2) = a.into();

  let b: BinaryTowers<4> = (a1, a2).into();

  assert_eq!(a, b);
}
