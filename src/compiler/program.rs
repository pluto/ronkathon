//! Creates a program from the parsed DSL output containing required polynomials used for PLONK
//! proving step.
//!
//! For selector polynomials, each constraint is broken down into `Gate` that supports equation:
//! `a(X)QL(X) + b(X)QR(X) + a(X)b(X)QM(X) + o(X)QO(X) + QC(X) = 0`.
//!
//! For permutation helpers, each variable usage over the constraints is accumulated and then placed
//! into respective [`Column`].

use std::collections::{HashMap, HashSet};

use super::{
  errors::{ParserError, ProgramError},
  utils::get_product_key,
};
use crate::{
  algebra::field::FiniteField,
  compiler::parser::{parse_constraints, WireCoeffs},
  polynomial::{Lagrange, Polynomial},
  Field, PlutoScalarField,
};

/// Column represents all three columns in the execution trace which a variable
/// can take.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Column {
  /// Left column, often representing left wire output in a gate
  LEFT = 1,
  /// Right column
  RIGHT,
  /// Output column
  OUTPUT,
}

impl From<u32> for Column {
  fn from(value: u32) -> Self {
    match value {
      1 => Self::LEFT,
      2 => Self::RIGHT,
      3 => Self::OUTPUT,
      _ => panic!("invalid value"),
    }
  }
}

/// `Cell` represents an item in the execution trace containing `row` and
/// `column` of the variable.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Cell {
  /// row of the variable in execution trace
  pub row:    u32,
  /// column of the variable, i.e. LEFT, RIGHT, OUTPUT
  pub column: Column,
}

impl Cell {
  /// Assign a domain value to a cell where `row` represents power of primitive root of unity and
  /// `column` represents coset value: $k*\omega^(row)$
  fn label(&self, group_order: usize) -> PlutoScalarField {
    let col: u32 = self.column as u32;
    PlutoScalarField::from(col)
      * PlutoScalarField::primitive_root_of_unity(group_order).pow(self.row as usize)
  }
}

/// `Program` represents constraints used while defining the arithmetic on the inputs
/// and group order of primitive roots of unity in the field.
#[derive(Debug, PartialEq)]
pub struct Program<'a, const GROUP_ORDER: usize> {
  /// `constraints` defined during arithmetic evaluation on inputs in the circuit
  constraints: Vec<WireCoeffs<'a>>,
  // order of multiplicative group formed by primitive roots of unity in the scalar field
  // group_order: usize,
}

/// Represents circuit related input which is apriori known to `Prover` and `Verifier` involved in
/// the process.
pub struct CommonPreprocessedInput<const GROUP_ORDER: usize> {
  /// multiplicative group order
  // group_order: usize,
  /// Q_L(X): left wire selector polynomial
  pub ql: Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
  /// Q_R(X): right wire selector polynomial
  pub qr: Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
  /// Q_M(X): multiplication gate selector polynomial
  pub qm: Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
  /// Q_O(X): output wire selector polynomial
  pub qo: Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
  /// Q_C(X): constant selector polynomial
  pub qc: Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
  /// S_σ1(X): first permutation polynomial
  pub s1: Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
  /// S_σ2(X): second permutation polynomial
  pub s2: Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
  /// S_σ3(X): third permutation polynomial
  pub s3: Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
}

impl<'a, const GROUP_ORDER: usize> Program<'a, GROUP_ORDER> {
  /// create a new [`Program`] from list of constraints and group order. Converts constraints into
  /// variables and their corresponding activation coefficients
  ///
  /// Assumes: group_order >= constraints.len()
  pub fn new(constraints: &[&'a str]) -> Result<Self, ProgramError<'a>> {
    let assembly: Result<Vec<WireCoeffs>, ParserError> =
      constraints.iter().map(|constraint| parse_constraints(constraint)).collect();

    let assembly = match assembly {
      Ok(wire_coeffs) => wire_coeffs,
      Err(parser_error) => return Err(ProgramError::ParserError(parser_error)),
    };

    Ok(Self { constraints: assembly })
  }

  /// returns selector polynomial used in execution trace for a gate
  #[allow(clippy::type_complexity)]
  fn selector_polynomials(
    &self,
  ) -> (
    Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
    Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
    Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
    Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
    Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
  ) {
    let mut l = [PlutoScalarField::ZERO; GROUP_ORDER];
    let mut r = [PlutoScalarField::ZERO; GROUP_ORDER];
    let mut m = [PlutoScalarField::ZERO; GROUP_ORDER];
    let mut o = [PlutoScalarField::ZERO; GROUP_ORDER];
    let mut c = [PlutoScalarField::ZERO; GROUP_ORDER];

    // iterate through the constraints and assign each selector value
    for (i, constraint) in self.constraints.iter().enumerate() {
      let gate = constraint.gate();
      (l[i], r[i], m[i], o[i], c[i]) = (gate.l, gate.r, gate.m, gate.o, gate.c);
    }
    let poly_l = Polynomial::<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>::new(l);
    let poly_r = Polynomial::<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>::new(r);
    let poly_m = Polynomial::<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>::new(m);
    let poly_o = Polynomial::<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>::new(o);
    let poly_c = Polynomial::<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>::new(c);
    (poly_l, poly_r, poly_m, poly_o, poly_c)
  }

  /// Returns `S1,S2,S3` polynomials used for creating permutation argument in PLONK
  #[allow(clippy::type_complexity)]
  fn s_polynomials(
    &self,
  ) -> (
    Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
    Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
    Polynomial<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>,
  ) {
    // captures uses of a variable in constraints where each new constraint defines a new row in
    // execution trace and columns represent left, right and output wires in a gate.
    // Map of variable and (row, column) tuples
    let mut variable_uses: HashMap<Option<&str>, HashSet<Cell>> =
      HashMap::from([(None, HashSet::new())]);

    // iterate through each constraint and wire and add its usage in respective variables
    for (row, constraint) in self.constraints.iter().enumerate() {
      // iterate through wires representing l, r, o columns
      for (column, value) in constraint.wires.iter().enumerate() {
        // get the variable used for that wire in respective constraint
        match variable_uses.get_mut(value) {
          // if already mapped, then add new (row, column) tuple to set
          Some(set) => {
            set.insert(Cell { row: row as u32, column: Column::from((column + 1) as u32) });
          },
          // if a new variable is found, create set and add tuple
          None => {
            let mut set = HashSet::new();
            set.insert(Cell { row: row as u32, column: Column::from((column + 1) as u32) });
            variable_uses.insert(*value, set);
          },
        };
      }
    }

    // add zero values for unfilled values
    for row in self.constraints.len()..GROUP_ORDER {
      let val = variable_uses.get_mut(&None).unwrap();
      val.insert(Cell { row: row as u32, column: Column::LEFT });
      val.insert(Cell { row: row as u32, column: Column::RIGHT });
      val.insert(Cell { row: row as u32, column: Column::OUTPUT });
    }

    // $S_i$ polynomial in evaluation form
    let mut s: [[PlutoScalarField; GROUP_ORDER]; 3] = [[PlutoScalarField::ZERO; GROUP_ORDER]; 3];

    // shift each polynomial value right by 1 and assign domain. for example:
    // let's say, usage of variable in execution trace looks like:
    // `[(1, LEFT), (2, RIGHT), (4, OUTPUT), (5, LEFT)]` then new usage is shifted by 1:
    // `[(5, LEFT), (1, LEFT), (2, RIGHT), (4, OUTPUT)]` and then assigned corresponding domain
    // value from roots of unity in field. This is done to ensure permutation of variables is
    // satisfied, i.e. variable at i+1th position is same as variable at ith position.
    for (_, uses) in variable_uses.into_iter() {
      let mut row_cols: Vec<Cell> = uses.into_iter().collect();
      row_cols.sort();

      for (i, cell) in row_cols.iter().enumerate() {
        let next_i = (i + 1) % row_cols.len();
        let next_column = row_cols[next_i].column as u32 - 1;
        let next_row = row_cols[next_i].row;
        s[next_column as usize][next_row as usize] = cell.label(GROUP_ORDER);
      }
    }

    // create polynomials in lagrange basis from variable values as evaluations
    let poly_s1 =
      Polynomial::<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>::new(s[0]);
    let poly_s2 =
      Polynomial::<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>::new(s[1]);
    let poly_s3 =
      Polynomial::<Lagrange<PlutoScalarField>, PlutoScalarField, GROUP_ORDER>::new(s[2]);
    (poly_s1, poly_s2, poly_s3)
  }

  /// creates selector and permutation helper polynomials from constraints as part of circuit
  /// preprocessing
  pub fn common_preprocessed_input(&self) -> CommonPreprocessedInput<GROUP_ORDER> {
    let (s1, s2, s3) = self.s_polynomials();
    let (ql, qr, qm, qo, qc) = self.selector_polynomials();
    CommonPreprocessedInput { ql, qr, qm, qo, qc, s1, s2, s3 }
  }

  /// returns public variables assigned in the circuit
  pub fn public_assignments(&self) -> Result<Vec<String>, ProgramError> {
    let mut variables = Vec::new();
    let mut flag = false;
    for wire_values in self.constraints.iter() {
      if wire_values.coeffs.get("$public") == Some(&1) {
        if flag {
          return Err(ProgramError::PublicAssignmentInvalidStatement);
        }
        let var_name: Vec<&String> =
          wire_values.coeffs.keys().filter(|key| !key.contains('$')).collect();
        assert_eq!(
          wire_values.coeffs.get(var_name[0]),
          Some(&-1),
          "incorrect coeffs: {}",
          var_name[0]
        );
        variables.push(var_name[0].clone());
      } else {
        flag = true;
      }
    }

    Ok(variables)
  }

  /// Evaluates the circuit and fill intermediate variable assignments
  pub fn evaluate_circuit(
    &'a self,
    starting_assignments: HashMap<Option<&'a str>, PlutoScalarField>,
  ) -> Result<HashMap<Option<&'a str>, PlutoScalarField>, ProgramError> {
    let mut out = starting_assignments.clone();
    out.insert(None, PlutoScalarField::ZERO);

    for constraint in self.constraints.iter() {
      let in_l = constraint.wires[0];
      let in_r = constraint.wires[1];
      let output = constraint.wires[2];

      let out_coeff = constraint.coeffs.get("$output_coeffs").unwrap_or(&1);
      let product_key = get_product_key(in_l.unwrap_or(""), in_r.unwrap_or(""));
      if output.is_some() && (*out_coeff == 1 || *out_coeff == -1) {
        let l_value = *out.get(&in_l).unwrap()
          * PlutoScalarField::from(*constraint.coeffs.get(in_l.unwrap_or("")).unwrap_or(&0));
        let r_value = *out.get(&in_r).unwrap()
          * PlutoScalarField::from(*constraint.coeffs.get(in_r.unwrap_or("")).unwrap_or(&0))
          * PlutoScalarField::from((in_l != in_r) as u32);
        let c_value = PlutoScalarField::from(*constraint.coeffs.get("$constant").unwrap_or(&0));
        let m_value = *out.get(&in_l).unwrap()
          * *out.get(&in_r).unwrap()
          * PlutoScalarField::from(*constraint.coeffs.get(&product_key).unwrap_or(&0));

        let output_value =
          (l_value + r_value + c_value + m_value) * PlutoScalarField::from(*out_coeff);

        match out.get(&output) {
          Some(out_value) =>
            if *out_value != output_value {
              // panic!("output value doesn't match, {}, {}", out_value, output_value);
              return Err(ProgramError::CircuitEvaluationOutputMismatch(*out_value, output_value));
            },
          None => {
            out.insert(output, output_value);
          },
        }
      }
    }

    Ok(out)
  }
}

#[cfg(test)]
mod tests {

  use rstest::{fixture, rstest};

  use super::*;

  #[fixture]
  fn constraint1<'a>() -> &'a [&'a str] {
    &["a public", "d === 9", "b <== a * a + 5", "c <== -2 * b - a * b"]
  }

  #[rstest]
  #[case(2, Column::LEFT, 2)]
  #[case(3, Column::RIGHT, 4)]
  #[case(4, Column::OUTPUT, 8)]
  fn cell_label(#[case] row: u32, #[case] column: Column, #[case] group_order: usize) {
    let cell = Cell { row, column };
    assert_eq!(
      cell.label(group_order),
      PlutoScalarField::primitive_root_of_unity(group_order).pow(row as usize)
        * PlutoScalarField::from(column as u32)
    )
  }

  #[test]
  fn new_program() {
    let constraints = &["a public", "b <== a * a"];
    let program = Program::<5>::new(constraints);
    assert!(program.is_ok());

    assert_eq!(program.unwrap(), Program {
      constraints: Vec::from([
        WireCoeffs {
          wires:  vec![Some("a"), None, None],
          coeffs: HashMap::from([
            (String::from("$public"), 1),
            (String::from("a"), -1),
            (String::from("$output_coeffs"), 0)
          ]),
        },
        WireCoeffs {
          wires:  vec![Some("a"), Some("a"), Some("b")],
          coeffs: HashMap::from([(String::from("a*a"), 1)]),
        }
      ]),
    })
  }

  #[rstest]
  fn s_polys(constraint1: &[&str]) {
    // TODO: make this more robust
    let program = Program::<4>::new(constraint1);

    assert!(program.is_ok());

    let program = program.unwrap();
    let (s1, s2, s3) = program.s_polynomials();

    assert_eq!(s1.coefficients.to_vec(), vec![
      PlutoScalarField::from(4),
      PlutoScalarField::from(3),
      PlutoScalarField::from(1),
      PlutoScalarField::from(15),
    ]);

    assert_eq!(s2.coefficients.to_vec(), vec![
      PlutoScalarField::from(9),
      PlutoScalarField::from(13),
      PlutoScalarField::from(16),
      PlutoScalarField::from(14),
    ]);

    assert_eq!(s3.coefficients.to_vec(), vec![
      PlutoScalarField::from(2),
      PlutoScalarField::from(5),
      PlutoScalarField::from(8),
      PlutoScalarField::from(12),
    ]);
  }

  #[test]
  fn selector_polys() {
    let constraint = &["a public", "d === 9", "b <== a * a + 5", "c <== -2 * b - a * b"];
    let program = Program::<4>::new(constraint);

    assert!(program.is_ok());
    let program = program.unwrap();

    let (ql, qr, qm, qo, qc) = program.selector_polynomials();
    assert_eq!(ql.coefficients.to_vec(), vec![
      PlutoScalarField::new(1), // first constraint, left variable is equal to 1
      PlutoScalarField::new(0), // second constraint, no left variable
      PlutoScalarField::new(0),
      PlutoScalarField::new(0),
    ]);
    assert_eq!(qr.coefficients.to_vec(), vec![
      PlutoScalarField::new(0),
      PlutoScalarField::new(0),
      PlutoScalarField::new(0),
      PlutoScalarField::new(2), // 4th constraint, right variable `b`'s coeff = -(-2) = 2
    ]);
    assert_eq!(qm.coefficients.to_vec(), vec![
      PlutoScalarField::new(0),
      PlutoScalarField::new(0),
      PlutoScalarField::from(-1), // 3rd constraint, `mul` variable = `a*a`, coeff = -(1)
      PlutoScalarField::new(1),   // 4th, `a*b` = -(-1)
    ]);
    assert_eq!(qo.coefficients.to_vec(), vec![
      PlutoScalarField::new(0),
      PlutoScalarField::new(1), // `d`: 1
      PlutoScalarField::new(1), // `b`: 1
      PlutoScalarField::new(1), // `c`: 1
    ]);
    assert_eq!(qc.coefficients.to_vec(), vec![
      PlutoScalarField::new(0),
      PlutoScalarField::new(17 - 9),
      PlutoScalarField::new(17 - 5),
      PlutoScalarField::new(0),
    ]);
  }

  #[rstest]
  #[case(&["a public", "d === 9", "b <== a * a + 5", "c <== -2 * b - a * b"], vec![String::from("a")])]
  #[case(&["d === 9"], vec![])]
  #[case(&["a public", "b public", "pq public", "b === pq", "c <== -a * b + 9", "pq <== a + b * -3"], vec![String::from("a"), String::from("b"), String::from("pq")])]
  #[should_panic]
  #[case(&["a public", "d === 9", "b <== a * a + 5", "b public", "c <== -2 * b - a * b"], vec![])]
  fn public_vars(#[case] constraint: &[&str], #[case] expected: Vec<String>) {
    let program = Program::<5>::new(constraint);
    assert!(program.is_ok());

    let program = program.unwrap();
    let public_vars = program.public_assignments();

    assert!(public_vars.is_ok());
    assert_eq!(public_vars.unwrap(), expected);
  }

  #[allow(unused_braces)]
  #[fixture]
  fn group_order_4() -> usize { 4 }

  #[allow(unused_braces)]
  #[fixture]
  fn group_order_8() -> usize { 8 }

  #[rstest]
  #[case(&["a public", "d === 9", "b <== a * a + 5", "c <== -2 * b - a * b"], vec![PlutoScalarField::from(2)], HashMap::from([(None, PlutoScalarField::from(0)), (Some("d"), PlutoScalarField::from(9)), (Some("a"), PlutoScalarField::from(2)), (Some("b"), PlutoScalarField::from(9)), (Some("c"), PlutoScalarField::from(-36))]))]
  #[should_panic]
  #[case(&["a public", "b === 9", "b <== a * a"], vec![PlutoScalarField::from(2)], HashMap::from([(None, PlutoScalarField::from(0)), (Some("a"), PlutoScalarField::from(2)), (Some("b"), PlutoScalarField::from(9))]))]
  fn evaluate_circuit_constraints(
    #[case] constraint1: &[&str],
    #[case] public_var_values: Vec<PlutoScalarField>,
    #[case] expected: HashMap<Option<&str>, PlutoScalarField>,
  ) {
    let program = Program::<4>::new(constraint1);
    assert!(program.is_ok());

    let program = program.unwrap();
    let public_vars = program.public_assignments();
    assert!(public_vars.is_ok());

    let public_vars = public_vars.unwrap();
    assert_eq!(public_vars.len(), public_var_values.len());

    let starting_assignments: HashMap<Option<&str>, PlutoScalarField> =
      HashMap::from_iter(public_vars.iter().map(|var| Some(var.as_str())).zip(public_var_values));
    let evaluations = program.evaluate_circuit(starting_assignments);

    assert!(evaluations.is_ok());

    assert_eq!(evaluations.unwrap(), expected);
  }

  // #[case(, group_order_8(), ,

  #[test]
  fn evaluate_circuit_constraints_with_group_order_8() {
    let public_var_values =
      vec![PlutoScalarField::from(2), PlutoScalarField::from(1), PlutoScalarField::from(1)];
    let expected = HashMap::from([
      (None, PlutoScalarField::from(0)),
      (Some("a"), PlutoScalarField::from(2)),
      (Some("b"), PlutoScalarField::from(1)),
      (Some("c"), PlutoScalarField::from(7)),
      (Some("pq"), PlutoScalarField::from(1)),
      (Some("e"), PlutoScalarField::from(-1)),
    ]);
    let constraints =
      &["a public", "b public", "pq public", "b === pq", "c <== -a * b + 9", "e <== a + b * -3"];
    let program = Program::<8>::new(constraints);
    assert!(program.is_ok());

    let program = program.unwrap();
    let public_vars = program.public_assignments();
    assert!(public_vars.is_ok());

    let public_vars = public_vars.unwrap();
    assert_eq!(public_vars.len(), public_var_values.len());

    let starting_assignments: HashMap<Option<&str>, PlutoScalarField> =
      HashMap::from_iter(public_vars.iter().map(|var| Some(var.as_str())).zip(public_var_values));
    let evaluations = program.evaluate_circuit(starting_assignments);

    assert!(evaluations.is_ok());

    assert_eq!(evaluations.unwrap(), expected);
  }
}
