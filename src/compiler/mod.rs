//! The compiler for `ronkathon` circuits.

// TODO: Remove this once the module is fleshed out.
#![allow(missing_docs)]
use petgraph::graph::{DiGraph, NodeIndex};

// TODO: Goal, allow someone to use this library to write rust to generate arithmetic circuits
// basically.
// ```
// use ronkathon::compiler::*;
//
// fn main() {
//   let a: Input = Variable::public(7);
//   let b: Input = Variable::private(3);
//   let b: Expression = a * c;
// }
// ```
// So we can do things like `impl Add`, `impl Mul` for variables and make them into gates?
use super::*;

pub mod dsl;

pub struct Wire {
  pub input:  Connection,
  pub output: Connection,
}

pub enum Connection {
  Input(Publicity),
  Output,
  Internal,
}

pub enum Publicity {
  Public(u32),
  Private(u32),
}

pub enum Operation {
  Add,
  Mul,
  Sub,
}

// TODO: Want to make it so gates own a reference for who they are connected to, and circuits own
// the gates. This way gates cannot be improperly connected to other gates.
pub struct Gate {
  pub left:   Wire,
  pub right:  Wire,
  pub output: Wire,
  pub op:     Operation,
}

pub struct Circuit {
  pub gates: DiGraph<Gate, Wire>,
}

impl Circuit {
  pub fn new() -> Self { Self { gates: DiGraph::new() } }
}

