use std::{error::Error, fmt::Display};

use crate::PlutoScalarField;

/// Errors from parsing the DSL
#[derive(Debug)]
pub enum ProgramError<'a> {
  PublicAssignmentInvalidStatement,
  CircuitEvaluationOutputMismatch(PlutoScalarField, PlutoScalarField),
  ParserError(ParserError<'a>),
}

impl<'a> Error for ProgramError<'a> {}

impl<'a> Display for ProgramError<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match *self {
      ProgramError::PublicAssignmentInvalidStatement =>
        write!(f, "public statements should be at the beginning"),
      ProgramError::CircuitEvaluationOutputMismatch(out_input_value, output_value) =>
        write!(f, "output value doesn't match: {} {}", out_input_value, output_value),
      ProgramError::ParserError(ref parser_error) =>
        write!(f, "program initialisation parser error: {}", parser_error),
    }
  }
}

#[derive(Debug)]
pub enum ParserError<'a> {
  EvaluateInvalidExpression(&'a str),
  EvaluateMultipleSubExpression(String),
  ConstraintsMaxVariables(Vec<&'a str>),
  ConstraintsInvalidCoefficientValues(String),
  ConstraintsUnsupportedValue(&'a str),
  ConstraintsInvalidVariableName(&'a str),
}

impl<'a> Error for ParserError<'a> {}

impl<'a> Display for ParserError<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match *self {
      ParserError::EvaluateInvalidExpression(expr) => write!(f, "invalid expression: {}", expr),
      ParserError::EvaluateMultipleSubExpression(ref expr) =>
        write!(f, "No ops: expected sub expr to be a unit: {}", expr),
      ParserError::ConstraintsMaxVariables(ref vars) =>
        write!(f, "max 2 variables allowed: {}", vars.join(" ")),
      ParserError::ConstraintsInvalidCoefficientValues(ref coeff_key) =>
        write!(f, "invalid coefficient value: {}", coeff_key),
      ParserError::ConstraintsUnsupportedValue(constraint) =>
        write!(f, "unsupported constraint token: {}", constraint),
      ParserError::ConstraintsInvalidVariableName(var) =>
        write!(f, "invalid variable name: {}", var),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compiler::{parser::parse_constraints, program::Program};

  #[test]
  fn program_error() {
    let constraints =
      &["a public", "d === 9", "b <== a * a + 5", "b public", "c <== -2 * b - a * b"];
    let program = Program::<5>::new(constraints).unwrap();

    let public_vars = program.public_assignments();

    assert!(
      matches!(public_vars, Err(ProgramError::PublicAssignmentInvalidStatement)),
      "public statements should be at the beginning"
    );
  }

  #[test]
  fn parser_error() {
    let constraint = "a <== b * c + d";
    let wire_values = parse_constraints(constraint);
    assert!(
      matches!(wire_values, Err(ParserError::ConstraintsMaxVariables(_))),
      "max 2 variables allowed",
    );
  }
}
