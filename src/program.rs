//! Creates a program from the parsed DSL output containing required polynomials used for PLONK
//! proving step.
use std::collections::{HashMap, HashSet};

use crate::{
  field::{gf_101::GF101, FiniteField},
  parser::{parse_constraints, WireValues},
  polynomial::{Lagrange, Polynomial},
};

/// Column represents all three columns in the execution trace which a variable
/// can take.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Column {
  /// Left column, often representing left wire output in a gate
  LEFT,
  /// Right column
  RIGHT,
  /// Output column
  OUTPUT,
}

// impl Into<u32> for Column {
//   fn into(self) -> u32 {
//     match self {
//       Self::LEFT => 0,
//       Self::RIGHT => 1,
//       Self::OUTPUT => 2,
//     }
//   }
// }

impl From<u32> for Column {
  fn from(value: u32) -> Self {
    match value {
      0 => Self::LEFT,
      1 => Self::RIGHT,
      2 => Self::OUTPUT,
      _ => panic!("invalid value"),
    }
  }
}

/// `Cell` represents an item in the execution trace containing `row` and
/// `column` of the variable.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Cell {
  /// row of the variable in execution trace
  pub row:    u32,
  /// column of the variable, i.e. LEFT, RIGHT, OUTPUT
  pub column: Column,
}

impl Cell {
  fn label(&self, group_order: u32) -> GF101 {
    let col: u32 = self.column as u32;
    GF101::primitive_root_of_unity(group_order).pow(self.row as u64 + col as u64)
  }
}

/// `Program` represents constraints used while defining the arithmetic on the inputs
/// and group order of primitive roots of unity in the field.
pub struct Program<'a> {
  /// `constraints` defined during arithmetic evaluation on inputs in the circuit
  constraints: Vec<WireValues<'a>>,
  /// order of multiplicative group formed by primitive roots of unity in the scalar field
  group_order: u32,
}

/// `CommonPreprocessedInput` represents circuit related input which is apriori known to `Prover`
/// and `Verifier` involved in the process.
pub struct CommonPreprocessedInput {
  group_order: u32,
  qm:          Polynomial<Lagrange<GF101>, GF101>,
  ql:          Polynomial<Lagrange<GF101>, GF101>,
  qr:          Polynomial<Lagrange<GF101>, GF101>,
  qc:          Polynomial<Lagrange<GF101>, GF101>,
  qo:          Polynomial<Lagrange<GF101>, GF101>,
  s1:          Polynomial<Lagrange<GF101>, GF101>,
  s2:          Polynomial<Lagrange<GF101>, GF101>,
  s3:          Polynomial<Lagrange<GF101>, GF101>,
}

impl<'a> Program<'a> {
  fn new(constraints: &[&'a str], group_order: u32) -> Self {
    let assembly = constraints
      .iter()
      .map(|constraint| parse_constraints(constraint))
      .collect::<Vec<WireValues>>();
    Self { constraints: assembly, group_order }
  }

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
    let mut variable_uses: HashMap<Option<&str>, HashSet<Cell>> =
      HashMap::from([(None, HashSet::new())]);
    for (row, constraint) in self.constraints.iter().enumerate() {
      for (column, value) in constraint.wires.iter().enumerate() {
        match variable_uses.get_mut(value) {
          Some(set) => {
            set.insert(Cell { row: row as u32, column: Column::from(column as u32) });
          },
          None => {
            let mut set = HashSet::new();
            set.insert(Cell { row: row as u32, column: Column::from(column as u32) });
            variable_uses.insert(*value, set);
          },
        };
      }
    }

    for row in self.constraints.len()..self.group_order as usize {
      let val = variable_uses.get_mut(&None).unwrap();
      for i in 0..3 {
        val.insert(Cell { row: row as u32, column: Column::from(i) });
      }
    }

    let mut s = vec![vec![GF101::ZERO; self.group_order as usize]; 3];

    for (_, uses) in variable_uses.into_iter() {
      let mut row_cols: Vec<Cell> = uses.into_iter().collect();
      row_cols.sort();

      for (i, cell) in row_cols.iter().enumerate() {
        let next_i = (i + 1) % row_cols.len();
        let next_column = row_cols[next_i].column as u32;
        let next_row = row_cols[next_i].row;
        s[next_column as usize][next_row as usize] = cell.label(self.group_order);
      }
    }

    let poly_s1 = Polynomial::<Lagrange<GF101>, GF101>::new(s[0].clone());
    let poly_s2 = Polynomial::<Lagrange<GF101>, GF101>::new(s[1].clone());
    let poly_s3 = Polynomial::<Lagrange<GF101>, GF101>::new(s[2].clone());
    (poly_s1, poly_s2, poly_s3)
  }

  fn common_preprocessed_input(&self) -> CommonPreprocessedInput {
    let (s1, s2, s3) = self.s_polynomials();
    let (ql, qr, qm, qo, qc) = self.selector_polynomials();
    CommonPreprocessedInput { group_order: self.group_order, ql, qr, qm, qo, qc, s1, s2, s3 }
  }

  /// returns public variables assigned in the circuit
  fn public_assignments(&self) -> Vec<String> {
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
  fn evaluate_circuit(&self) -> HashMap<String, u32> { todo!() }
}
