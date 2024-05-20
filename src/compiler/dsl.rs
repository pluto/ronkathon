use super::*;

#[derive(Clone, Copy, Debug)]
pub enum Input {
  Variable(Variable),
  Public(usize),
  Private(usize),
}

#[derive(Clone, Copy, Debug)]
pub struct Variable {
  pub label: usize,
}

#[derive(Clone, Copy, Debug)]
pub enum Expression<ExpL, ExpR> {
  Add(ExpL, ExpR),
  Mul(ExpL, ExpR),
}

impl Add for Input {
  type Output = Expression<Input, Input>;

  fn add(self, rhs: Self) -> Self::Output { Expression::Add(self, rhs) }
}

impl<ExpL, ExpR> Add<Expression<ExpL, ExpR>> for Input {
  type Output = Expression<Input, Expression<ExpL, ExpR>>;

  fn add(self, rhs: Expression<ExpL, ExpR>) -> Self::Output { Expression::Add(self, rhs) }
}

impl<ExpL, ExpR> Add<Input> for Expression<ExpL, ExpR> {
  type Output = Expression<Expression<ExpL, ExpR>, Input>;

  fn add(self, rhs: Input) -> Self::Output { Expression::Add(self, rhs) }
}

impl<ExpL1, ExpR1, ExpL2, ExpR2> Add<Expression<ExpL2, ExpR2>> for Expression<ExpL1, ExpR1> {
  type Output = Expression<Expression<ExpL1, ExpR1>, Expression<ExpL2, ExpR2>>;

  fn add(self, rhs: Expression<ExpL2, ExpR2>) -> Self::Output { Expression::Add(self, rhs) }
}

impl Mul for Input {
  type Output = Expression<Input, Input>;

  fn mul(self, rhs: Self) -> Self::Output { Expression::Mul(self, rhs) }
}

impl<ExpL, ExpR> Mul<Expression<ExpL, ExpR>> for Input {
  type Output = Expression<Input, Expression<ExpL, ExpR>>;

  fn mul(self, rhs: Expression<ExpL, ExpR>) -> Self::Output { Expression::Mul(self, rhs) }
}

impl<ExpL, ExpR> Mul<Input> for Expression<ExpL, ExpR> {
  type Output = Expression<Expression<ExpL, ExpR>, Input>;

  fn mul(self, rhs: Input) -> Self::Output { Expression::Mul(self, rhs) }
}

impl<ExpL1, ExpR1, ExpL2, ExpR2> Mul<Expression<ExpL2, ExpR2>> for Expression<ExpL1, ExpR1> {
  type Output = Expression<Expression<ExpL1, ExpR1>, Expression<ExpL2, ExpR2>>;

  fn mul(self, rhs: Expression<ExpL2, ExpR2>) -> Self::Output { Expression::Mul(self, rhs) }
}

impl Display for Input {
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    match self {
      Input::Variable(val) => write!(f, "x_{}", val.label),
      Input::Public(val) => write!(f, "{}", val),
      Input::Private(val) => write!(f, "{}", val),
    }
  }
}

impl<ExpL: Display, ExpR: Display> Display for Expression<ExpL, ExpR> {
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    match self {
      Expression::Add(left, right) => write!(f, "({} + {})", left, right),
      Expression::Mul(left, right) => write!(f, "({} * {})", left, right),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn writing_a_program() {
    // Create two variables
    let a = Input::Public(7);
    let b = Input::Private(3);
    let x = Input::Variable(Variable { label: 0 });

    // Create basic expressions with these variables
    let add_ab = a + b;
    println!("{}", add_ab);
    assert_eq!(format!("{}", add_ab), "(7 + 3)");

    let mul_ab = a * b;
    println!("{}", mul_ab);
    assert_eq!(format!("{}", mul_ab), "(7 * 3)");

    // Check that we can add a variable to an expression
    println!("{}", a + mul_ab);
    assert_eq!(format!("{}", a + mul_ab), "(7 + (7 * 3))");

    // Check that we can add an expression to a variable
    println!("{}", mul_ab + a);
    assert_eq!(format!("{}", mul_ab + a), "((7 * 3) + 7)");

    // Check that we can add two expressions together
    println!("{}", add_ab + mul_ab);
    assert_eq!(format!("{}", add_ab + mul_ab), "((7 + 3) + (7 * 3))");

    // Check that we can multiply an expression by a variable
    println!("{}", mul_ab * x);
    assert_eq!(format!("{}", mul_ab * x), "((7 * 3) * x_0)");
  }
}
