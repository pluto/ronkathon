use super::*;
use crate::field::binary::extension::{multiply, num_digits, to_bool_vec};

fn from_bool_vec(num: Vec<BinaryField>) -> u64 {
  let mut result: u64 = 0;
  for (i, &bit) in num.iter().rev().enumerate() {
    if bit.0 == 1 {
      result |= 1 << (num.len() - 1 - i);
    }
  }
  result
}

#[test]
fn field_arithmetic() {
  let a = BinaryField::new(0);
  let b = BinaryField::new(1);
  let c = a + b;
  assert_eq!(c, b);
}

#[test]
fn test_num_digits() {
  let digits = num_digits(4);
  assert_eq!(digits, 3);
}

#[test]
fn multiply_vec() {
  let a = vec![BinaryField::new(1)];
  let b = vec![BinaryField::new(1)];
  let res = multiply(a, b, 0);
  assert_eq!(res, vec![BinaryField::new(1)]);

  let a = to_bool_vec(160);
  let b = to_bool_vec(23);
  assert_eq!(a.len(), 8);
  assert_eq!(a.len(), b.len());
  println!("{:?}", a);

  assert_eq!(from_bool_vec(a.clone()), 160);
  assert_eq!(from_bool_vec(b.clone()), 23);

  let res = multiply(a, b, 3);
  let num = from_bool_vec(res);
  println!("{}", num);
}
