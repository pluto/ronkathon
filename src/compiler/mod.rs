//! The compiler for `ronkathon` circuits.

// TODO: Remove this once the module is fleshed out.
#![allow(missing_docs)]

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

use std::array;

// Above seems done. Now we need to have a way to unravel a collection of expressions into a
// circuit that may have the same inputs and outputs as the expressions. Inputs are going to be
// the terminal variables found by fully unravelling expressions and they should be named. The
// fully ravelled expressions are the outputs, and they can also be named
use super::*;

pub mod dsl;
pub use dsl::*;

#[derive(Debug, Clone, Copy)]
pub struct Circuit<const INPUTS: usize> {
  pub inputs: [Input; INPUTS],
}

impl<const INPUTS: usize> Circuit<INPUTS> {
  pub fn new() -> Self {
    Self { inputs: array::from_fn(|label| Input::Variable(Variable { label })) }
  }

  pub const fn input(&self, label: usize) -> Input { self.inputs[label] }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn creating_a_circuit() {
    let circuit = Circuit::<3>::new();
    let x_0 = circuit.input(0);
    let x_1 = circuit.input(1);
    let x_2 = circuit.input(2);

    let expr = x_0 * x_1 + x_2;
    println!("{}", expr);
  }
}
