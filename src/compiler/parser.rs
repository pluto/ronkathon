//! Parses a simple DSL used to define circuits.
//! ## Rules:
//! - supports `<==` for assignment and `===` for arithmetic equality checks
//! - mark variables as public in the beginning.
//! - only supports quadratic constraints, i.e. don't support `y <== x * x * x`.
//! - each token should be separated by space.
//!
//! Outputs parsed output in form of [`WireCoeffs`] values and coefficients.
//!
//! ## Example
//! - `a public` =>                    `(['a', None, None], {'$public': 1, 'a': -1,
//!   '$output_coeffs': 0}`
//! - `b <== a * c` =>                 `(['a', 'c', 'b'], {'a*c': 1})`
//! - `d <== a * c - 45 * a + 987` =>  `(['a', 'c', 'd'], {'a*c': 1, 'a': -45, '': 987})`
// TODOs:
// - incorrect use of &str and String
// - use iterators more
// - substitute panics with result and errors
// - do proper trimming of string while evaluating into coeffs

use std::{
  collections::{HashMap, HashSet},
  iter,
};

use super::utils::{get_product_key, is_valid_var_name};
use crate::field::{gf_101::GF101, FiniteField};

/// Fan-in 2 Gate representing a constraint in the computation.
/// Each constraint satisfies PLONK's arithmetic equation: `a(X)QL(X) + b(X)QR(X) + a(X)b(X)QM(X) +
/// o(X)QO(X) + QC(X) = 0`.
pub struct Gate {
  /// left wire value
  pub l: GF101,
  /// right wire value
  pub r: GF101,
  /// output wire, represented as `$output_coeffs` in wire coefficients
  pub o: GF101,
  /// multiplication wire
  pub m: GF101,
  /// constant wire, represented as `$constant` in coefficients
  pub c: GF101,
}

/// Values of wires with coefficients of each wire name
#[derive(Debug, PartialEq)]
pub struct WireCoeffs<'a> {
  /// variable used in each wire
  pub wires:  Vec<Option<&'a str>>,
  /// coefficients of variables in wires and [`Gate`]
  pub coeffs: HashMap<String, i32>,
}

impl<'a> WireCoeffs<'a> {
  fn l(&self) -> GF101 {
    match self.wires[0] {
      Some(wire) => match self.coeffs.get(wire) {
        Some(val) => -GF101::from(*val),
        None => GF101::ZERO,
      },
      None => GF101::ZERO,
    }
  }

  fn r(&self) -> GF101 {
    if self.wires[0].is_some() && self.wires[1].is_some() && self.wires[0] != self.wires[1] {
      match self.coeffs.get(self.wires[1].unwrap()) {
        Some(val) => -GF101::from(*val),
        None => GF101::ZERO,
      }
    } else {
      GF101::ZERO
    }
  }

  fn o(&self) -> GF101 {
    match self.coeffs.get("$output_coeffs") {
      Some(val) => GF101::from(*val),
      None => GF101::ONE,
    }
  }

  fn c(&self) -> GF101 {
    match self.coeffs.get("$constant") {
      Some(val) => -GF101::from(*val),
      None => GF101::ZERO,
    }
  }

  fn m(&self) -> GF101 {
    match (self.wires[0], self.wires[1]) {
      (Some(a), Some(b)) => match self.coeffs.get(&get_product_key(a, b)) {
        Some(val) => -GF101::from(*val),
        None => GF101::ZERO,
      },
      _ => GF101::ZERO,
    }
  }

  /// sends gate activation coefficients from each wires.
  pub fn gate(&self) -> Gate {
    Gate { l: self.l(), r: self.r(), o: self.o(), m: self.m(), c: self.c() }
  }
}

/// Converts an arithmetic expression containing numbers, variables and `{+, -, *}`
/// into a mapping of term to coefficient
///
/// For example:
/// `['a', '+', 'b', '*', 'c', '*', '5']` becomes `{'a': 1, 'b*c': 5}`
///
/// Note that this is a recursive algo, so the input can be a mix of tokens and
/// mapping expressions
fn evaluate(exprs: &[&str], first_is_neg: bool) -> HashMap<String, i32> {
  let index_plus = exprs.iter().position(|&r| r == "+");
  if let Some(index) = index_plus {
    let l = evaluate(&exprs[..index], first_is_neg);
    let r = evaluate(&exprs[index + 1..], false);
    let l_keys: Vec<String> = l.keys().cloned().collect();
    let r_keys: Vec<String> = r.keys().cloned().collect();
    let mut key_set: HashSet<String> = HashSet::from_iter(l_keys);
    key_set.extend(r_keys);

    let mut res = HashMap::new();
    // let _ = key_set
    //   .into_iter()
    //   .map(|key| res.insert(key.clone(), l.get(&key).unwrap_or(&0) + r.get(&key).unwrap_or(&0)));
    for key in key_set.into_iter() {
      let l_val = l.get(&key).unwrap_or(&0);
      let r_val = r.get(&key).unwrap_or(&0);
      res.insert(key.clone(), l_val + r_val);
    }
    return res;
  }

  let index_minus = exprs.iter().position(|&r| r == "-");
  if let Some(index) = index_minus {
    let l = evaluate(&exprs[..index], first_is_neg);
    let r = evaluate(&exprs[index + 1..], true);
    let l_keys: Vec<String> = l.keys().cloned().collect();
    let r_keys: Vec<String> = r.keys().cloned().collect();
    let mut key_set: HashSet<String> = HashSet::from_iter(l_keys);
    key_set.extend(r_keys);

    let mut res = HashMap::new();
    // let _ = key_set
    //   .into_iter()
    //   .map(|key| res.insert(key.clone(), l.get(&key).unwrap_or(&0) - r.get(&key).unwrap_or(&0)));
    for key in key_set.into_iter() {
      let l_val = l.get(&key).unwrap_or(&0);
      let r_val = r.get(&key).unwrap_or(&0);
      res.insert(key.clone(), l_val + r_val);
    }
    return res;
  }

  let index_mul = exprs.iter().position(|&r| r == "*");
  if let Some(index) = index_mul {
    let l = evaluate(&exprs[..index], first_is_neg);
    let r = evaluate(&exprs[index + 1..], false);

    let mut res = HashMap::new();
    for (k1, v1) in l.iter() {
      for (k2, v2) in r.iter() {
        res.insert(get_product_key(k1, k2), v1 * v2);
      }
    }
    return res;
  }

  if exprs.len() > 1 {
    panic!("No ops: expected sub expr to be a unit");
  } else if exprs[0].starts_with('-') {
    return evaluate(&[&exprs[0][1..]], !first_is_neg);
  } else if exprs[0].trim().parse::<i32>().is_ok() {
    let num = exprs[0].trim().parse::<i32>().unwrap_or(0);
    let sign = if first_is_neg { -1 } else { 1 };
    return HashMap::from([("$constant".to_string(), num * sign)]);
  } else if is_valid_var_name(exprs[0]) {
    let sign = if first_is_neg { -1 } else { 1 };
    return HashMap::from([(exprs[0].to_string(), sign)]);
  } else {
    panic!("invalid expression: {}", exprs[0]);
  }
}

/// Parse constraints into [`WireCoeffs`] containing wires and corresponding coefficients.
///
/// ## Example
///
/// valid equations, and output:
/// - `a === 9` =>                     `([None, None, 'a'], {'': 9})`
/// - `a public` =>                    `(['a', None, None], {'$public': 1, 'a': -1,
///   '$output_coeffs': 0}`
/// - `b <== a * c` =>                 `(['a', 'c', 'b'], {'a*c': 1})`
/// - `d <== a * c - 45 * a + 987` =>  `(['a', 'c', 'd'], {'a*c': 1, 'a': -45, '': 987})`
///
/// invalid equations:
/// - `7 === 7`             =>         # Can't assign to non-variable
/// - `a <== b * * c`       =>         # Two times signs in a row
/// - `e <== a + b * c * d` =>         # Multiplicative degree > 2
pub fn parse_constraints(constraint: &str) -> WireCoeffs {
  let tokens: Vec<&str> = constraint.trim().trim_end_matches('\n').split(' ').collect();
  if tokens[1] == "<==" || tokens[1] == "===" {
    let mut out = tokens[0];
    let mut coeffs = evaluate(&tokens[2..], false);
    if out.starts_with('-') {
      out = &out[1..];
      coeffs.insert("$output_coeffs".to_string(), -1);
    }

    let mut variables: Vec<&str> = tokens
      .into_iter()
      .skip(2)
      .map(|var| var.trim_start_matches('-'))
      .filter(|name| is_valid_var_name(name))
      .collect::<HashSet<&str>>()
      .into_iter()
      .collect();
    variables.sort();

    let mut allowed_coeffs_set: HashSet<String> =
      HashSet::from_iter(variables.iter().map(|var| var.to_string()));
    allowed_coeffs_set.extend(["$output_coeffs".to_string(), "$constant".to_string()]);

    match variables.len() {
      0 => {},
      1 => {
        variables.push(variables[0]);
        allowed_coeffs_set.insert(get_product_key(variables[0], variables[0]));
      },
      2 => {
        allowed_coeffs_set.insert(get_product_key(variables[0], variables[1]));
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

    WireCoeffs { wires, coeffs }
  } else if tokens[1] == "public" {
    let coeffs = HashMap::from([
      (tokens[0].to_string(), -1),
      (String::from("$output_coeffs"), 0),
      (String::from("$public"), 1),
    ]);

    return WireCoeffs { wires: vec![Some(tokens[0]), None, None], coeffs };
  } else {
    panic!("unsupported value: {}", constraint);
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn wire_values() {
    let wire_values = WireCoeffs {
      wires:  vec![Some("a"), Some("b"), Some("c")],
      coeffs: HashMap::from([
        (String::from("$output_coeffs"), 2),
        (String::from("a"), -1),
        (String::from("$constant"), 9),
      ]),
    };
    let gate = wire_values.gate();
    assert_eq!(gate.l, -GF101::from(-1));
    assert_eq!(gate.r, GF101::ZERO);
    assert_eq!(gate.m, GF101::ZERO);
    assert_eq!(gate.o, GF101::from(2));
    assert_eq!(gate.c, -GF101::from(9));

    let wire_values = WireCoeffs {
      wires:  vec![Some("a"), Some("b"), Some("c")],
      coeffs: HashMap::from([(String::from("b"), -1), (String::from("a*b"), -9)]),
    };
    let gate = wire_values.gate();
    assert_eq!(gate.l, -GF101::ZERO);
    assert_eq!(gate.r, -GF101::from(-1));
    assert_eq!(gate.m, -GF101::from(-9));
    assert_eq!(gate.o, GF101::ONE);
    assert_eq!(gate.c, -GF101::ZERO);

    let wire_values = WireCoeffs {
      wires:  vec![Some("a"), None, None],
      coeffs: HashMap::from([
        (String::from("$output"), 1),
        (String::from("a"), -1),
        (String::from("$output_coeffs"), 0),
      ]),
    };
    let gate = wire_values.gate();
    assert_eq!(gate.l, GF101::ONE);
    assert_eq!(gate.r, GF101::ZERO);
    assert_eq!(gate.m, GF101::ZERO);
    assert_eq!(gate.o, GF101::ZERO);
    assert_eq!(gate.c, GF101::ZERO);
  }

  #[test]
  fn evaluate_expression() {
    let expr = ["a", "+", "b", "*", "c", "*", "5"];
    let res = evaluate(&expr, false);
    assert_eq!(res, HashMap::from([("a".to_string(), 1), ("b*c".to_string(), 5)]));

    let expr = ["a"];
    let res = evaluate(&expr, false);
    assert_eq!(res, HashMap::from([("a".to_string(), 1)]));

    let expr = ["a"];
    let res = evaluate(&expr, false);
    assert_eq!(res, HashMap::from([("a".to_string(), 1)]));

    let expr = ["a", "*", "b", "*", "c", "*", "d"];
    let res = evaluate(&expr, false);
    assert_eq!(res, HashMap::from([("a*b*c*d".to_string(), 1)]));

    let expr = ["a", "+", "b", "-", "-c", "*", "-d"];
    let res = evaluate(&expr, false);
    assert_eq!(
      res,
      HashMap::from([("a".to_string(), 1), ("b".to_string(), 1), ("c*d".to_string(), -1)])
    );

    let expr = ["-10", "+", "c", "*", "-8", "-", "11"];
    let res = evaluate(&expr, false);
    assert_eq!(res, HashMap::from([("c".to_string(), -8), ("$constant".to_string(), -21)]));

    let expr = ["-2", "*", "b", "-", "a", "*", "b"];
    let res = evaluate(&expr, false);
    assert_eq!(res, HashMap::from([("a*b".to_string(), -1), ("b".to_string(), -2)]));
  }

  #[test]
  fn circuit_parse_constraints() {
    let wire_values = parse_constraints("a <== b * c");
    assert_eq!(wire_values, WireCoeffs {
      wires:  vec![Some("b"), Some("c"), Some("a")],
      coeffs: HashMap::from([(String::from("b*c"), 1)]),
    });

    let wire_values = parse_constraints("a public");
    assert_eq!(wire_values, WireCoeffs {
      wires:  vec![Some("a"), None, None],
      coeffs: HashMap::from([
        (String::from("$output_coeffs"), 0),
        (String::from("$public"), 1),
        (String::from("a"), -1)
      ]),
    });

    let wire_values = parse_constraints("a === 9");
    assert_eq!(wire_values, WireCoeffs {
      wires:  vec![None, None, Some("a")],
      coeffs: HashMap::from([(String::from("$constant"), 9)]),
    });

    let wire_values = parse_constraints("b <== a + 9 * 10");
    assert_eq!(wire_values, WireCoeffs {
      wires:  vec![Some("a"), Some("a"), Some("b")],
      coeffs: HashMap::from([(String::from("a"), 1), (String::from("$constant"), 90)]),
    });

    let wire_values = parse_constraints("-a <== b * -c * -9 - 10");
    assert_eq!(wire_values, WireCoeffs {
      wires:  vec![Some("b"), Some("c"), Some("a")],
      coeffs: HashMap::from([
        (String::from("$output_coeffs"), -1),
        (String::from("b*c"), 9),
        (String::from("$constant"), -10)
      ]),
    });
  }
}
