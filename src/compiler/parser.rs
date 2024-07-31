//! Parses a simple DSL used to define circuits.
//! ## Rules:
//! - supports `<==` for assignment and `===` for arithmetic equality checks
//! - mark variables as public in the beginning.
//! - only supports quadratic constraints, i.e. don't support `y <== x * x * x`.
//! - each token should be separated by space.
//!
//! Outputs parsed output in form of [`WireCoeffs`] values and coefficients.
//! - `wires`: represent variables corresponding to gate wires in each constraint.
//! - `coefficients`: coefficient corresponding to each variable.
//!
//! ## Note
//!
//! Some default coefficients are used for certain constraints:
//! - `$constant`: for constant variables
//! - `$output_coeffs`: for output variables. Example: `-a <== b * b` has `$output_coeffs` as `-1`
//! - `$public`: for public variable declarations
//!
//! ## Example
//! - `a public` =>                    `(['a', None, None], {'$public': 1, 'a': -1,
//!   '$output_coeffs': 0}`
//! - `b <== a * c` =>                 `(['a', 'c', 'b'], {'a*c': 1})`
//! - `d <== a * c - 45 * a + 987` =>  `(['a', 'c', 'd'], {'a*c': 1, 'a': -45, '': 987})`

use std::{
  collections::{HashMap, HashSet},
  iter,
};

use super::{
  errors::ParserError,
  utils::{get_product_key, is_valid_var_name},
};
use crate::{Field, PlutoScalarField};

/// Fan-in 2 Gate representing a constraint in the computation.
/// Each constraint satisfies PLONK's arithmetic equation: `a(X)QL(X) + b(X)QR(X) + a(X)b(X)QM(X) +
/// o(X)QO(X) + QC(X) = 0`.
pub struct Gate {
  /// left wire value
  pub l: PlutoScalarField,
  /// right wire value
  pub r: PlutoScalarField,
  /// output wire, represented as `$output_coeffs` in wire coefficients
  pub o: PlutoScalarField,
  /// multiplication wire
  pub m: PlutoScalarField,
  /// constant wire, represented as `$constant` in coefficients
  pub c: PlutoScalarField,
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
  fn l(&self) -> PlutoScalarField {
    match self.wires[0] {
      Some(wire) => match self.coeffs.get(wire) {
        // negation is done to satisfy constraint equation of vanilla plonk
        Some(val) => -PlutoScalarField::from(*val),
        None => PlutoScalarField::ZERO,
      },
      None => PlutoScalarField::ZERO,
    }
  }

  fn r(&self) -> PlutoScalarField {
    if self.wires[0].is_some() && self.wires[1].is_some() && self.wires[0] != self.wires[1] {
      match self.coeffs.get(self.wires[1].unwrap()) {
        // negation is done to satisfy constraint equation of vanilla plonk
        Some(val) => -PlutoScalarField::from(*val),
        None => PlutoScalarField::ZERO,
      }
    } else {
      PlutoScalarField::ZERO
    }
  }

  fn o(&self) -> PlutoScalarField {
    match self.coeffs.get("$output_coeffs") {
      Some(val) => PlutoScalarField::from(*val),
      None => PlutoScalarField::ONE,
    }
  }

  fn c(&self) -> PlutoScalarField {
    match self.coeffs.get("$constant") {
      Some(val) => -PlutoScalarField::from(*val),
      None => PlutoScalarField::ZERO,
    }
  }

  fn m(&self) -> PlutoScalarField {
    match (self.wires[0], self.wires[1]) {
      (Some(a), Some(b)) => match self.coeffs.get(&get_product_key(a, b)) {
        Some(val) => -PlutoScalarField::from(*val),
        None => PlutoScalarField::ZERO,
      },
      _ => PlutoScalarField::ZERO,
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
/// mapping expressions.
fn evaluate<'a>(
  exprs: &[&'a str],
  first_is_neg: bool,
) -> Result<HashMap<String, i32>, ParserError<'a>> {
  let index_plus = exprs.iter().position(|&r| r == "+");
  if let Some(index) = index_plus {
    let l = evaluate(&exprs[..index], first_is_neg)?;
    let r = evaluate(&exprs[index + 1..], false)?;
    let l_keys: Vec<String> = l.keys().cloned().collect();
    let r_keys: Vec<String> = r.keys().cloned().collect();
    let mut key_set: HashSet<String> = HashSet::from_iter(l_keys);
    key_set.extend(r_keys);

    let mut res = HashMap::new();
    for key in key_set.into_iter() {
      let l_val = l.get(&key).unwrap_or(&0);
      let r_val = r.get(&key).unwrap_or(&0);
      res.insert(key.clone(), l_val + r_val);
    }
    return Ok(res);
  }

  let index_minus = exprs.iter().position(|&r| r == "-");
  if let Some(index) = index_minus {
    let l = evaluate(&exprs[..index], first_is_neg)?;
    let r = evaluate(&exprs[index + 1..], true)?;
    let l_keys: Vec<String> = l.keys().cloned().collect();
    let r_keys: Vec<String> = r.keys().cloned().collect();
    let mut key_set: HashSet<String> = HashSet::from_iter(l_keys);
    key_set.extend(r_keys);

    let mut res = HashMap::new();
    for key in key_set.into_iter() {
      let l_val = l.get(&key).unwrap_or(&0);
      let r_val = r.get(&key).unwrap_or(&0);
      res.insert(key.clone(), l_val + r_val);
    }
    return Ok(res);
  }

  let index_mul = exprs.iter().position(|&r| r == "*");
  if let Some(index) = index_mul {
    let l = evaluate(&exprs[..index], first_is_neg)?;
    let r = evaluate(&exprs[index + 1..], false)?;

    let mut res = HashMap::new();
    for (k1, v1) in l.iter() {
      for (k2, v2) in r.iter() {
        res.insert(get_product_key(k1, k2), v1 * v2);
      }
    }
    return Ok(res);
  }

  if exprs.len() > 1 {
    return Err(ParserError::EvaluateMultipleSubExpression(exprs.join(" ").to_string()));
  } else if exprs[0].starts_with('-') {
    return evaluate(&[&exprs[0][1..]], !first_is_neg);
  } else if exprs[0].trim().parse::<i32>().is_ok() {
    let num = exprs[0].trim().parse::<i32>().unwrap_or(0);
    let sign = if first_is_neg { -1 } else { 1 };
    return Ok(HashMap::from([("$constant".to_string(), num * sign)]));
  } else if is_valid_var_name(exprs[0]) {
    let sign = if first_is_neg { -1 } else { 1 };
    return Ok(HashMap::from([(exprs[0].to_string(), sign)]));
  } else {
    return Err(ParserError::EvaluateInvalidExpression(exprs[0]));
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
/// - `d <== a * c - 45 * a + 987` =>  `(['a', 'c', 'd'], {'a*c': 1, 'a': -45, '$constant': 987})`
///
/// invalid equations:
/// - `7 === 7`             =>         # Can't assign to non-variable
/// - `a <== b * * c`       =>         # Two times signs in a row
/// - `e <== a + b * c * d` =>         # Multiplicative degree > 2
pub fn parse_constraints(constraint: &str) -> Result<WireCoeffs, ParserError> {
  // split into tokens by spaces
  let tokens: Vec<&str> = constraint.trim().trim_end_matches('\n').split(' ').collect();

  // parse assignment or arithmetic checks
  if tokens[1] == "<==" || tokens[1] == "===" {
    // first token is the output
    let mut out = tokens[0];

    // parse rest of the constraints
    let mut coeffs = evaluate(&tokens[2..], false)?;

    // handle output's negative coefficient
    if out.starts_with('-') {
      out = &out[1..];
      coeffs.insert("$output_coeffs".to_string(), -1);
    }

    // handle valid output variable name
    if !is_valid_var_name(out) {
      return Err(ParserError::ConstraintsInvalidVariableName(out));
    }

    // parse all valid variables
    let mut variables: Vec<&str> = tokens
      .into_iter()
      .skip(2)
      .map(|var| var.trim_start_matches('-'))
      .filter(|name| is_valid_var_name(name))
      .collect::<HashSet<&str>>()
      .into_iter()
      .collect();
    variables.sort();

    // create set of all allowed variables
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
      _ => return Err(ParserError::ConstraintsMaxVariables(variables)),
    }

    // check if valid coeff values
    for key in coeffs.keys() {
      if !allowed_coeffs_set.contains::<String>(key) {
        return Err(ParserError::ConstraintsInvalidCoefficientValues(key.clone()));
      }
    }

    let variables_len = variables.len();

    // get wire variable names
    let mut wires: Vec<Option<&str>> =
      variables.into_iter().map(Some).chain(iter::repeat(None).take(2 - variables_len)).collect();

    // output variable is in last wire
    wires.push(Some(out));

    Ok(WireCoeffs { wires, coeffs })
  } else if tokens[1] == "public" {
    // parse public constraint
    let coeffs = HashMap::from([
      (tokens[0].to_string(), -1),
      (String::from("$output_coeffs"), 0),
      (String::from("$public"), 1),
    ]);

    return Ok(WireCoeffs { wires: vec![Some(tokens[0]), None, None], coeffs });
  } else {
    return Err(ParserError::ConstraintsUnsupportedValue(constraint));
  }
}

#[cfg(test)]
mod tests {

  use rstest::rstest;

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
    assert_eq!(gate.l, -PlutoScalarField::from(-1));
    assert_eq!(gate.r, PlutoScalarField::ZERO);
    assert_eq!(gate.m, PlutoScalarField::ZERO);
    assert_eq!(gate.o, PlutoScalarField::from(2));
    assert_eq!(gate.c, -PlutoScalarField::from(9));

    let wire_values = WireCoeffs {
      wires:  vec![Some("a"), Some("b"), Some("c")],
      coeffs: HashMap::from([(String::from("b"), -1), (String::from("a*b"), -9)]),
    };
    let gate = wire_values.gate();
    assert_eq!(gate.l, -PlutoScalarField::ZERO);
    assert_eq!(gate.r, -PlutoScalarField::from(-1));
    assert_eq!(gate.m, -PlutoScalarField::from(-9));
    assert_eq!(gate.o, PlutoScalarField::ONE);
    assert_eq!(gate.c, -PlutoScalarField::ZERO);

    let wire_values = WireCoeffs {
      wires:  vec![Some("a"), None, None],
      coeffs: HashMap::from([
        (String::from("$output"), 1),
        (String::from("a"), -1),
        (String::from("$output_coeffs"), 0),
      ]),
    };
    let gate = wire_values.gate();
    assert_eq!(gate.l, PlutoScalarField::ONE);
    assert_eq!(gate.r, PlutoScalarField::ZERO);
    assert_eq!(gate.m, PlutoScalarField::ZERO);
    assert_eq!(gate.o, PlutoScalarField::ZERO);
    assert_eq!(gate.c, PlutoScalarField::ZERO);
  }

  #[rstest]
  #[case(&["a", "+", "b", "*", "c", "*", "5"], HashMap::from([("a".to_string(), 1), ("b*c".to_string(), 5)]))]
  #[case(&["a"], HashMap::from([("a".to_string(), 1)]))]
  #[case(&["a", "*", "b", "*", "c", "*", "d"], HashMap::from([("a*b*c*d".to_string(), 1)]))]
  #[case(&["a", "+", "b", "-", "-c", "*", "-d"], HashMap::from([("a".to_string(), 1), ("b".to_string(), 1), ("c*d".to_string(), -1)]))]
  #[case(&["-10", "+", "c", "*", "-8", "-", "11"], HashMap::from([("c".to_string(), -8), ("$constant".to_string(), -21)]))]
  #[case(&["-2", "*", "b", "-", "a", "*", "b"], HashMap::from([("a*b".to_string(), -1), ("b".to_string(), -2)]))]
  #[should_panic]
  #[case(&["a", "+", "b", "c"], HashMap::from([]))]
  #[should_panic(expected = "assertion")]
  #[case(&["b", "/", "+"], HashMap::from([]))]
  fn evaluate_expression(#[case] expr: &[&str], #[case] expected: HashMap<String, i32>) {
    let res = evaluate(expr, false);
    assert!(res.is_ok());
    assert_eq!(res.unwrap(), expected);
  }

  #[rstest]
  #[case("a <== b * c", vec![Some("b"), Some("c"), Some("a")], HashMap::from([(String::from("b*c"), 1)]))]
  #[case("a public", vec![Some("a"), None, None], HashMap::from([(String::from("$output_coeffs"), 0), (String::from("$public"), 1), (String::from("a"), -1)]))]
  #[case("a === 9", vec![None, None, Some("a")], HashMap::from([(String::from("$constant"), 9)]))]
  #[case("b <== a + 9 * 10", vec![Some("a"), Some("a"), Some("b")], HashMap::from([(String::from("a"), 1), (String::from("$constant"), 90)]))]
  #[case("-a <== b * -c * -9 - 10", vec![Some("b"), Some("c"), Some("a")], HashMap::from([(String::from("$output_coeffs"), -1), (String::from("b*c"), 9), (String::from("$constant"), -10)]))]
  #[case("x2 <== x * x", vec![Some("x"), Some("x"), Some("x2")], HashMap::from([(String::from("x*x"), 1)]))]
  #[should_panic]
  #[case("a <== b * c + d", vec![], HashMap::from([]))]
  #[should_panic(expected = "assertion")]
  #[case("8 === 9", vec![], HashMap::from([]))]
  #[should_panic(expected = "index")]
  #[case("a <== b * * c", vec![], HashMap::from([]))]
  fn circuit_parse_constraints(
    #[case] constraint: &str,
    #[case] expected_wires: Vec<Option<&str>>,
    #[case] expected_coeffs: HashMap<String, i32>,
  ) {
    let wire_values = parse_constraints(constraint);
    assert!(wire_values.is_ok());
    assert_eq!(wire_values.unwrap(), WireCoeffs {
      wires:  expected_wires,
      coeffs: expected_coeffs,
    });
  }
}
