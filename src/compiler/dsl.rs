use super::*;

#[derive(Clone, Copy, Debug)]
pub enum Variable {
  Public(u32),
  Private(u32),
}

#[derive(Clone, Copy, Debug)]
pub enum Expression<ExpL, ExpR> {
  Add(ExpL, ExpR),
  Mul(ExpL, ExpR),
}

impl Add for Variable {
  type Output = Expression<Variable, Variable>;

  fn add(self, rhs: Self) -> Self::Output { Expression::Add(self, rhs) }
}

impl<ExpL, ExpR> Add<Expression<ExpL, ExpR>> for Variable {
  type Output = Expression<Variable, Expression<ExpL, ExpR>>;

  fn add(self, rhs: Expression<ExpL, ExpR>) -> Self::Output { Expression::Add(self, rhs) }
}

impl<ExpL, ExpR> Add<Variable> for Expression<ExpL, ExpR> {
  type Output = Expression<Expression<ExpL, ExpR>, Variable>;

  fn add(self, rhs: Variable) -> Self::Output { Expression::Add(self, rhs) }
}

impl<EXP1, EXP2, EXP3, EXP4> Add<Expression<EXP3, EXP4>> for Expression<EXP1, EXP2> {
  type Output = Expression<Expression<EXP1, EXP2>, Expression<EXP3, EXP4>>;

  fn add(self, rhs: Expression<EXP3, EXP4>) -> Self::Output { Expression::Add(self, rhs) }
}

impl Mul for Variable {
  type Output = Expression<Variable, Variable>;

  fn mul(self, rhs: Self) -> Self::Output { Expression::Mul(self, rhs) }
}

impl<ExpL, ExpR> Mul<Expression<ExpL, ExpR>> for Variable {
  type Output = Expression<Variable, Expression<ExpL, ExpR>>;

  fn mul(self, rhs: Expression<ExpL, ExpR>) -> Self::Output { Expression::Mul(self, rhs) }
}

impl<ExpL, ExpR> Mul<Variable> for Expression<ExpL, ExpR> {
  type Output = Expression<Expression<ExpL, ExpR>, Variable>;

  fn mul(self, rhs: Variable) -> Self::Output { Expression::Mul(self, rhs) }
}

impl<EXP1, EXP2, EXP3, EXP4> Mul<Expression<EXP3, EXP4>> for Expression<EXP1, EXP2> {
  type Output = Expression<Expression<EXP1, EXP2>, Expression<EXP3, EXP4>>;

  fn mul(self, rhs: Expression<EXP3, EXP4>) -> Self::Output { Expression::Mul(self, rhs) }
}

impl Display for Variable {
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    match self {
      Variable::Public(val) => write!(f, "{}", val),
      Variable::Private(val) => write!(f, "{}", val),
    }
  }
}

impl<EXPL: Display, EXPR: Display> Display for Expression<EXPL, EXPR> {
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
    let a = Variable::Public(7);
    let b = Variable::Private(3);

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
  }
}
