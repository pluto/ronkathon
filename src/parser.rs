//! Parses a simple DSL used to define circuits.

// TODOs:
// - incorrect use of &str and String
// - use iterators more

use std::{
  collections::{HashMap, HashSet},
  iter,
};

use crate::field::{gf_101::GF101, FiniteField};

/// Gate represents each new constraint in the computation
pub struct Gate {
  /// left wire value
  pub l: GF101,
  /// right wire value
  pub r: GF101,
  /// output wire
  pub o: GF101,
  /// multiplication wire
  pub m: GF101,
  /// constant wire
  pub c: GF101,
}

/// Values of wires with coefficients of each wire name
pub struct WireValues<'a> {
  /// variable used in each wire
  pub wires:  Vec<Option<&'a str>>,
  /// coefficients of variables in wires
  pub coeffs: HashMap<String, i32>,
}

impl<'a> WireValues<'a> {
  fn l(&self) -> GF101 {
    let l = match self.coeffs.get(self.wires[0].unwrap()) {
      Some(val) => -GF101::from(*val),
      None => GF101::ZERO,
    };
    l
  }

  fn r(&self) -> GF101 {
    let r = match self.coeffs.get(self.wires[1].unwrap()) {
      Some(val) => -GF101::from(*val),
      None => GF101::ZERO,
    };
    r
  }

  fn o(&self) -> GF101 {
    let o = match self.coeffs.get("$output_coeffs") {
      Some(val) => GF101::from(*val),
      None => GF101::ZERO,
    };
    o
  }

  fn c(&self) -> GF101 {
    let c = match self.coeffs.get("") {
      Some(val) => -GF101::from(*val),
      None => GF101::ZERO,
    };
    c
  }

  fn m(&self) -> GF101 {
    let m = match self.coeffs.get(&get_product_key(self.wires[0].unwrap(), self.wires[1].unwrap()))
    {
      Some(val) => -GF101::from(*val),
      None => GF101::ZERO,
    };
    m
  }

  /// sends
  pub fn gate(&self) -> Gate {
    Gate { l: self.l(), r: self.r(), o: self.o(), m: self.m(), c: self.c() }
  }
}

// impl<'a> GateWires<'a> {
//   fn from_slice(x: Vec<Option<&'a str>>) -> Self {
//     debug_assert!(x.len() == 3);
//     GateWires { l: x[0], r: x[1], o: x[2] }
//   }
// }

fn get_product_key(a: &str, b: &str) -> String {
  let mut a_star: Vec<&str> = a.split('*').collect();
  a_star.append(&mut b.split('*').collect());

  a_star.sort();
  a_star.join("*")
}

fn evaluate(exprs: &[&str], first_is_neg: bool) -> HashMap<String, i32> {
  // let index_plus = exprs.iter().position(|&r| r == "+");
  // match index_plus {
  //     Some(index) => {

  //     },
  //     None => {

  //     }
  // }
  todo!()
}
fn is_valid_var_name(name: &str) -> bool {
  let name0 = name.as_bytes()[0];
  !name.is_empty() && name.chars().all(char::is_alphanumeric) && (48u8..=57u8).contains(&name0)
}
/// Example valid equations, and output:
/// a === 9                      ([None, None, 'a'], {'': 9})
/// b <== a * c                  (['a', 'c', 'b'], {'a*c': 1})
/// d <== a * c - 45 * a + 987   (['a', 'c', 'd'], {'a*c': 1, 'a': -45, '': 987})
///
/// Example invalid equations:
/// 7 === 7                      # Can't assign to non-variable
/// a <== b * * c                # Two times signs in a row
/// e <== a + b * c * d          # Multiplicative degree > 2
pub fn parse_constraints(constraint: &str) -> WireValues {
  let tokens: Vec<&str> = constraint.trim().strip_suffix('\n').unwrap().split(' ').collect();
  if tokens[1] == "<==" || tokens[1] == "===" {
    let mut out = tokens[0];
    let mut coeffs = evaluate(&tokens[2..], false);
    let out_bytes = out.as_bytes()[0];
    if out_bytes == "-".as_bytes()[0] {
      // TODO: very shady
      out = &out[1..];
      coeffs.insert("$output_coeffs".to_string(), -1);
    }

    let mut variables: Vec<&str> = tokens
      .into_iter()
      .skip(2)
      .map(|var| var.strip_prefix('-').unwrap())
      .filter(|name| is_valid_var_name(name))
      .collect::<HashSet<&str>>()
      .into_iter()
      .collect();

    let mut allowed_coeffs =
      variables.clone().into_iter().map(|s| s.to_string()).collect::<Vec<String>>();
    allowed_coeffs.append(&mut vec!["output_coeffs".to_string(), "".to_string()]);

    let allowed_coeffs_set: HashSet<String> = HashSet::from_iter(allowed_coeffs.clone());

    match variables.len() {
      0 => panic!("can't be empty"),
      1 => {
        variables.push(variables[0]);
        allowed_coeffs.push(get_product_key(variables[0], variables[0]));
      },
      2 => {
        allowed_coeffs.push(get_product_key(variables[0], variables[1]));
      },
      _ => panic!("max 2 variables allowed"),
    }

    // check if valid coeff values
    for key in coeffs.keys() {
      if !allowed_coeffs_set.contains(key) {
        panic!("disallowed value");
      }
    }

    let variables_len = variables.len();
    let mut wires: Vec<Option<&str>> =
      variables.into_iter().map(Some).chain(iter::repeat(None).take(2 - variables_len)).collect();
    wires.push(Some(out));

    WireValues { wires, coeffs }
  } else if tokens[1] == "public" {
    let coeffs = HashMap::from([
      (tokens[0].to_string(), -1),
      (String::from("$output_coeffs"), 0),
      (String::from("$output"), 1),
    ]);

    return WireValues { wires: vec![Some(tokens[0]), None, None], coeffs };
  } else {
    panic!("unsupported value");
  }
}
