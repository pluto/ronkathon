//! Creates a program from the parsed DSL output containing required polynomials used for PLONK
//! proving step.
//!
//! For selector polynomials, each constraint is broken down into `Gate` that supports equation:
//! `a(X)QL(X) + b(X)QR(X) + a(X)b(X)QM(X) + o(X)QO(X) + QC(X) = 0`.
//!
//! For permutation helpers, each variable usage over the constraints is accumulated and then placed
//! into respective [`Column`].

use std::collections::{HashMap, HashSet};

use super::utils::get_product_key;
use crate::{
  compiler::parser::{parse_constraints, WireCoeffs},
  field::{gf_101::GF101, FiniteField},
  polynomial::{Lagrange, Polynomial},
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
  /// Assign a domain value to a cell where `row` represents power of primtive root of unity and
  /// `column` represents coset value: $k*\omega^(row)$
  fn label(&self, group_order: u32) -> GF101 {
    let col: u32 = self.column as u32;
    GF101::from(col) * GF101::primitive_root_of_unity(group_order).pow(self.row as u64)
  }
}

/// `Program` represents constraints used while defining the arithmetic on the inputs
/// and group order of primitive roots of unity in the field.
#[derive(Debug, PartialEq)]
pub struct Program<'a> {
  /// `constraints` defined during arithmetic evaluation on inputs in the circuit
  constraints: Vec<WireCoeffs<'a>>,
  /// order of multiplicative group formed by primitive roots of unity in the scalar field
  group_order: u32,
}

/// `CommonPreprocessedInput` represents circuit related input which is apriori known to `Prover`
/// and `Verifier` involved in the process.
pub struct CommonPreprocessedInput {
  /// multiplicative group order
  pub group_order: u32,
  /// Q_L(X): left wire selector polynomial
  pub ql:          Polynomial<Lagrange<GF101>, GF101>,
  /// Q_R(X): right wire selector polynomial
  pub qr:          Polynomial<Lagrange<GF101>, GF101>,
  /// Q_M(X): multiplication gate selector polynomial
  pub qm:          Polynomial<Lagrange<GF101>, GF101>,
  /// Q_O(X): output wire selector polynomial
  pub qo:          Polynomial<Lagrange<GF101>, GF101>,
  /// Q_C(X): constant selector polynomial
  pub qc:          Polynomial<Lagrange<GF101>, GF101>,
  /// S_σ1(X): first permutation polynomial
  pub s1:          Polynomial<Lagrange<GF101>, GF101>,
  /// S_σ2(X): second permutation polynomial
  pub s2:          Polynomial<Lagrange<GF101>, GF101>,
  /// S_σ3(X): third permutation polynomial
  pub s3:          Polynomial<Lagrange<GF101>, GF101>,
}

impl<'a> Program<'a> {
  /// create a new [`Program`] from list of constraints and group order. Converts constraints into
  /// variables and their corresponding activation coefficients
  ///
  /// Assumes: group_order >= constraints.len()
  pub fn new(constraints: &[&'a str], group_order: u32) -> Self {
    let assembly = constraints
      .iter()
      .map(|constraint| parse_constraints(constraint))
      .collect::<Vec<WireCoeffs>>();
    Self { constraints: assembly, group_order }
  }

  /// returns selector polynomial used in execution trace for a gate
  fn selector_polynomials(
    &self,
  ) -> (
    Polynomial<Lagrange<GF101>, GF101>,
    Polynomial<Lagrange<GF101>, GF101>,
    Polynomial<Lagrange<GF101>, GF101>,
    Polynomial<Lagrange<GF101>, GF101>,
    Polynomial<Lagrange<GF101>, GF101>,
  ) {
    let mut l = vec![GF101::ZERO; self.group_order as usize];
    let mut r = vec![GF101::ZERO; self.group_order as usize];
    let mut m = vec![GF101::ZERO; self.group_order as usize];
    let mut o = vec![GF101::ZERO; self.group_order as usize];
    let mut c = vec![GF101::ZERO; self.group_order as usize];

    // iterate through the constraints and assign each selector value
    for (i, constraint) in self.constraints.iter().enumerate() {
      let gate = constraint.gate();
      (l[i], r[i], m[i], o[i], c[i]) = (gate.l, gate.r, gate.m, gate.o, gate.c);
    }

    let poly_l = Polynomial::<Lagrange<GF101>, GF101>::new(l);
    let poly_r = Polynomial::<Lagrange<GF101>, GF101>::new(r);
    let poly_m = Polynomial::<Lagrange<GF101>, GF101>::new(m);
    let poly_o = Polynomial::<Lagrange<GF101>, GF101>::new(o);
    let poly_c = Polynomial::<Lagrange<GF101>, GF101>::new(c);
    (poly_l, poly_r, poly_m, poly_o, poly_c)
  }

  /// Returns `S1,S2,S3` polynomials used for creating permutation argument in PLONK
  fn s_polynomials(
    &self,
  ) -> (
    Polynomial<Lagrange<GF101>, GF101>,
    Polynomial<Lagrange<GF101>, GF101>,
    Polynomial<Lagrange<GF101>, GF101>,
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
    for row in self.constraints.len()..self.group_order as usize {
      let val = variable_uses.get_mut(&None).unwrap();
      val.insert(Cell { row: row as u32, column: Column::LEFT });
      val.insert(Cell { row: row as u32, column: Column::RIGHT });
      val.insert(Cell { row: row as u32, column: Column::OUTPUT });
    }

    // $S_i$ polynomial in evaluation form
    let mut s = vec![vec![GF101::ZERO; self.group_order as usize]; 3];

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
        s[next_column as usize][next_row as usize] = cell.label(self.group_order);
      }
    }

    // create polynomials in lagrange basis from variable values as evaluations
    let poly_s1 = Polynomial::<Lagrange<GF101>, GF101>::new(s[0].clone());
    let poly_s2 = Polynomial::<Lagrange<GF101>, GF101>::new(s[1].clone());
    let poly_s3 = Polynomial::<Lagrange<GF101>, GF101>::new(s[2].clone());
    (poly_s1, poly_s2, poly_s3)
  }

  /// creates selector and permutation helper polynomials from constraints as part of circuit
  /// preprocessing
  pub fn common_preprocessed_input(&self) -> CommonPreprocessedInput {
    let (s1, s2, s3) = self.s_polynomials();
    let (ql, qr, qm, qo, qc) = self.selector_polynomials();
    CommonPreprocessedInput { group_order: self.group_order, ql, qr, qm, qo, qc, s1, s2, s3 }
  }

  /// returns public variables assigned in the circuit
  pub fn public_assignments(&self) -> Vec<String> {
    let mut variables = Vec::new();
    let mut flag = false;
    for wire_values in self.constraints.iter() {
      if wire_values.coeffs.get("$public") == Some(&1) {
        if flag {
          panic!("public values should be at top");
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

    variables
  }

  /// Evaluates the circuit and fill intermediate variable assignments
  pub fn evaluate_circuit(
    &'a self,
    starting_assignments: HashMap<Option<&'a str>, GF101>,
  ) -> HashMap<Option<&'a str>, GF101> {
    let mut out = starting_assignments.clone();
    out.insert(None, GF101::ZERO);

    for constraint in self.constraints.iter() {
      let in_l = constraint.wires[0];
      let in_r = constraint.wires[1];
      let output = constraint.wires[2];

      let out_coeff = constraint.coeffs.get("$output_coeffs").unwrap_or(&1);
      let product_key = get_product_key(in_l.unwrap_or(""), in_r.unwrap_or(""));
      if output.is_some() && (*out_coeff == 1 || *out_coeff == -1) {
        let l_value = *out.get(&in_l).unwrap()
          * GF101::from(*constraint.coeffs.get(in_l.unwrap_or("")).unwrap_or(&0));
        let r_value = *out.get(&in_r).unwrap()
          * GF101::from(*constraint.coeffs.get(in_r.unwrap_or("")).unwrap_or(&0))
          * GF101::from((in_l != in_r) as u32);
        let c_value = GF101::from(*constraint.coeffs.get("$constant").unwrap_or(&0));
        let m_value = *out.get(&in_l).unwrap()
          * *out.get(&in_r).unwrap()
          * GF101::from(*constraint.coeffs.get(&product_key).unwrap_or(&0));

        let output_value = (l_value + r_value + c_value + m_value) * GF101::from(*out_coeff);

        match out.get(&output) {
          Some(out_value) =>
            if *out_value != output_value {
              panic!("output value doesn't match, {}, {}", out_value, output_value);
            },
          None => {
            out.insert(output, output_value);
          },
        }
      }
    }

    out
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
  #[case(2, Column::LEFT, 5)]
  #[case(3, Column::RIGHT, 4)]
  #[case(4, Column::OUTPUT, 10)]
  fn cell_label(#[case] row: u32, #[case] column: Column, #[case] group_order: u32) {
    let cell = Cell { row, column };
    assert_eq!(
      cell.label(group_order),
      GF101::primitive_root_of_unity(group_order).pow(row as u64) * GF101::from(column as u32)
    )
  }

  #[test]
  fn new_program() {
    let constraints = &["a public", "b <== a * a"];
    let program = Program::new(constraints, 5);
    assert_eq!(program, Program {
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
      group_order: 5,
    })
  }

  #[rstest]
  fn s_polys(constraint1: &[&str]) {
    let program = Program::new(constraint1, 5);
    let (s1, s2, s3) = program.s_polynomials();
    // println!("{:?}", s1.coefficients);
    // println!("{:?}", s2.coefficients);
    // println!("{:?}", s3.coefficients);
    let prou = GF101::primitive_root_of_unity(5);
    let mut hmap: HashMap<GF101, Cell> = HashMap::new();
    for i in 0..5 {
      let prou = prou.pow(i);
      let c1 = prou * GF101::new(Column::LEFT as u32);
      hmap.insert(c1, Cell { row: i as u32, column: Column::LEFT });
      let c2 = prou * GF101::new(Column::RIGHT as u32);
      hmap.insert(c2, Cell { row: i as u32, column: Column::RIGHT });
      let c3 = prou * GF101::new(Column::OUTPUT as u32);
      hmap.insert(c3, Cell { row: i as u32, column: Column::OUTPUT });
    }
    // println!("{:?}", hmap);

    let mut s1_cell =
      s1.coefficients.iter().map(|coeff| *hmap.get(coeff).unwrap()).collect::<Vec<Cell>>();
    let mut s2_cell =
      s2.coefficients.iter().map(|coeff| *hmap.get(coeff).unwrap()).collect::<Vec<Cell>>();
    let mut s3_cell =
      s3.coefficients.iter().map(|coeff| *hmap.get(coeff).unwrap()).collect::<Vec<Cell>>();
    println!("s1: {:?}\ns2: {:?}\ns3: {:?}", s1_cell, s2_cell, s3_cell);

    let s1_cell_left = s1_cell.remove(0);
    s1_cell.push(s1_cell_left);
    let s2_cell_left = s2_cell.remove(0);
    s2_cell.push(s2_cell_left);
    let s3_cell_left = s3_cell.remove(0);
    s3_cell.push(s3_cell_left);
    println!("s1: {:?}\ns2: {:?}\ns3: {:?}", s1_cell, s2_cell, s3_cell);
    // assert_eq!(s1.coefficients, vec![
    //   GF101::from(0),
    //   GF101::from(2),
    //   GF101::from(0),
    //   GF101::from(36),
    //   GF101::from(95)
    // ]);
  }

  #[test]
  fn selector_polys() {
    let constraint = &["a public", "d === 9", "b <== a * a + 5", "c <== -2 * b - a * b"];
    let program = Program::new(constraint, 5);
    let (ql, qr, qm, qo, qc) = program.selector_polynomials();
    assert_eq!(ql.coefficients, vec![
      GF101::new(1),
      GF101::new(0),
      GF101::new(0),
      GF101::new(0),
      GF101::new(0)
    ]);
    assert_eq!(qr.coefficients, vec![
      GF101::new(0),
      GF101::new(0),
      GF101::new(0),
      GF101::new(2),
      GF101::new(0)
    ]);
    assert_eq!(qm.coefficients, vec![
      GF101::new(0),
      GF101::new(0),
      GF101::new(100),
      GF101::new(1),
      GF101::new(0),
    ]);
    assert_eq!(qo.coefficients, vec![
      GF101::new(0),
      GF101::new(1),
      GF101::new(1),
      GF101::new(1),
      GF101::new(0)
    ]);
    assert_eq!(qc.coefficients, vec![
      GF101::new(0),
      GF101::new(101 - 9),
      GF101::new(101 - 5),
      GF101::new(0),
      GF101::new(0)
    ]);
  }

  #[rstest]
  #[case(&["a public", "d === 9", "b <== a * a + 5", "c <== -2 * b - a * b"], vec![String::from("a")])]
  #[case(&["d === 9"], vec![])]
  #[case(&["a public", "b public", "pq public", "b === pq", "c <== -a * b + 9", "pq <== a + b * -3"], vec![String::from("a"), String::from("b"), String::from("pq")])]
  #[should_panic]
  #[case(&["a public", "d === 9", "b <== a * a + 5", "b public", "c <== -2 * b - a * b"], vec![])]
  fn public_vars(#[case] constraint: &[&str], #[case] expected: Vec<String>) {
    let program = Program::new(constraint, 5);
    let public_vars = program.public_assignments();
    assert_eq!(public_vars, expected);
  }

  #[rstest]
  #[case(&["a public", "d === 9", "b <== a * a + 5", "c <== -2 * b - a * b"], 5, vec![GF101::from(2)],
  HashMap::from([(None, GF101::from(0)), (Some("d"), GF101::from(9)), (Some("a"), GF101::from(2)), (Some("b"), GF101::from(9)),
  (Some("c"), GF101::from(-36))]))]
  #[case(&["a public", "b public", "pq public", "b === pq", "c <== -a * b + 9", "e <== a + b * -3"],
  10, vec![GF101::from(2), GF101::from(1), GF101::from(1)], HashMap::from([(None, GF101::from(0)), (Some("a"), GF101::from(2)), (Some("b"), GF101::from(1)), (Some("c"), GF101::from(7)), (Some("pq"), GF101::from(1)), (Some("e"), GF101::from(100))]))]
  fn evaluate_circuit_constraints(
    #[case] constraint1: &[&str],
    #[case] group_order: u32,
    #[case] public_var_values: Vec<GF101>,
    #[case] expected: HashMap<Option<&str>, GF101>,
  ) {
    let program = Program::new(constraint1, group_order);
    let public_vars = program.public_assignments();

    assert_eq!(public_vars.len(), public_var_values.len());
    let starting_assignments: HashMap<Option<&str>, GF101> =
      HashMap::from_iter(public_vars.iter().map(|var| Some(var.as_str())).zip(public_var_values));
    let evaluations = program.evaluate_circuit(starting_assignments);
    assert_eq!(evaluations, expected);
  }
}
