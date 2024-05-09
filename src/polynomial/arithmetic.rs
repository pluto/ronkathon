use std::array;

use super::*;

// TODO: Implement `Mul`, `MulAssign`, `Product`.
// * `Mul` and other products will require FFT.

impl<F: FiniteField> Add for Polynomial<Monomial, F> {
  type Output = Self;

  fn add(self, rhs: Self) -> Self {
    let d = self.degree().max(rhs.degree());
    let mut coefficients = vec![F::ZERO; d + 1];
    for i in 0..d + 1 {
      coefficients[i] = *self.coefficients.get(i).unwrap_or(&F::ZERO)
        + *rhs.coefficients.get(i).unwrap_or(&F::ZERO);
    }
    Self { coefficients, basis: self.basis }
  }
}

impl<F: FiniteField> AddAssign for Polynomial<Monomial, F> {
  fn add_assign(&mut self, mut rhs: Self) {
    let d = self.degree().max(rhs.degree());
    let mut coefficients = vec![F::ZERO; d + 1];
    if self.degree() < d {
      self.coefficients.resize(d + 1, F::ZERO);
    } else {
      rhs.coefficients.resize(d + 1, F::ZERO);
    }
    for i in 0..d + 1 {
      self.coefficients[i] += rhs.coefficients[i];
    }
  }
}

impl<F: FiniteField> Sum for Polynomial<Monomial, F> {
  fn sum<I: Iterator<Item = Self>>(iter: I) -> Self { iter.reduce(|x, y| x + y).unwrap() }
}

impl<F: FiniteField> Sub for Polynomial<Monomial, F> {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self {
    let d = self.degree().max(rhs.degree());
    let mut coefficients = vec![F::ZERO; d + 1];
    for i in 0..d + 1 {
      coefficients[i] = *self.coefficients.get(i).unwrap_or(&F::ZERO)
        - *rhs.coefficients.get(i).unwrap_or(&F::ZERO);
    }
    Self { coefficients, basis: self.basis }
  }
}

impl<F: FiniteField> SubAssign for Polynomial<Monomial, F> {
  fn sub_assign(&mut self, mut rhs: Self) {
    let d = self.degree().max(rhs.degree());
    let mut coefficients = vec![F::ZERO; d + 1];
    if self.degree() < d {
      self.coefficients.resize(d + 1, F::ZERO);
    } else {
      rhs.coefficients.resize(d + 1, F::ZERO);
    }
    for i in 0..d + 1 {
      self.coefficients[i] -= rhs.coefficients[i];
    }
  }
}

impl<F: FiniteField> Neg for Polynomial<Monomial, F> {
  type Output = Self;

  fn neg(self) -> Self {
    Self {
      coefficients: self.coefficients.into_iter().map(|c| -c).collect(),
      basis:        self.basis,
    }
  }
}

impl<F: FiniteField> Div for Polynomial<Monomial, F> {
  type Output = Self;

  fn div(self, rhs: Self) -> Self::Output {
    // // Euclidean division
    // // Initial quotient value
    // let mut q = F::zero();

    // // Initial remainder value is our numerator polynomial
    // let mut p = self;

    // // Leading coefficient of the denominator
    // let c = rhs.leading_coefficient();

    // // Create quotient poly
    // let mut diff = p.degree() as isize - rhs.degree() as isize;
    // if diff < 0 {
    //   return Polynomial::<Monomial, F>::new(vec![F::zero(); 1]);
    // }
    // let mut q_coeffs = vec![F::zero(); diff as usize + 1];

    // while diff >= 0 {
    //   let s = p.leading_coefficient() * c.inverse().unwrap();
    //   q_coeffs[diff as usize] = s;
    //   p -= rhs.pow_mult(s, diff as usize);
    //   p.trim_zeros();
    //   diff -= 1;
    // }
    // Polynomial::<Monomial, F>::new(q_coeffs)
    self.quotient_and_remainder(rhs).0
  }
}

impl<F: FiniteField> Rem for Polynomial<Monomial, F> {
  type Output = Self;

  fn rem(self, rhs: Self) -> Self { self.quotient_and_remainder(rhs).1 }
}

#[cfg(test)]
mod tests {
  use field::gf_101::GF101;

  use super::*;

  fn poly_a() -> Polynomial<Monomial, GF101> {
    Polynomial::<Monomial, GF101>::new(vec![
      GF101::new(1),
      GF101::new(2),
      GF101::new(3),
      GF101::new(4),
    ])
  }

  fn poly_b() -> Polynomial<Monomial, GF101> {
    Polynomial::<Monomial, GF101>::new(vec![
      GF101::new(5),
      GF101::new(6),
      GF101::new(7),
      GF101::new(8),
      GF101::new(9),
    ])
  }

  #[test]
  fn add() {
    let c = poly_a() + poly_b();
    println!("{:?}", c.coefficients);
    assert_eq!(c.coefficients, [
      GF101::new(6),
      GF101::new(8),
      GF101::new(10),
      GF101::new(12),
      GF101::new(9)
    ]);
  }

  #[test]
  fn add_assign() {
    let mut a = poly_a();
    a += poly_b();
    assert_eq!(a.coefficients, [
      GF101::new(6),
      GF101::new(8),
      GF101::new(10),
      GF101::new(12),
      GF101::new(9)
    ]);
  }

  #[test]
  fn sum() {
    let sum = [poly_a(), poly_b()].into_iter().sum::<Polynomial<Monomial, GF101>>();
    assert_eq!(sum.coefficients, [
      GF101::new(6),
      GF101::new(8),
      GF101::new(10),
      GF101::new(12),
      GF101::new(9)
    ]);
  }

  #[test]
  fn sub() {
    let c = poly_a() - poly_b();
    assert_eq!(c.coefficients, [
      GF101::new(97),
      GF101::new(97),
      GF101::new(97),
      GF101::new(97),
      GF101::new(92)
    ]);
  }

  #[test]
  fn sub_assign() {
    let mut a = poly_a();
    a -= poly_b();
    assert_eq!(a.coefficients, [
      GF101::new(97),
      GF101::new(97),
      GF101::new(97),
      GF101::new(97),
      GF101::new(92)
    ]);
  }

  #[test]
  fn neg() {
    let a = -poly_a();
    assert_eq!(a.coefficients, [GF101::new(100), GF101::new(99), GF101::new(98), GF101::new(97)]);
  }

  #[test]
  fn div() {
    println!("poly_a: {}", poly_a());
    println!("poly_b: {}", poly_b());
    let q_ab = poly_a() / poly_b();
    assert_eq!(q_ab.coefficients, [GF101::new(0)]);

    let q_ba = poly_b() / poly_a();
    assert_eq!(q_ba.coefficients, [GF101::new(95), GF101::new(78)]);
    println!("q_ba coefficients: {:?}", q_ba.coefficients);

    let p = Polynomial::<Monomial, GF101>::new(vec![GF101::new(1), GF101::new(2), GF101::new(1)]);
    println!("p: {}", p);
    let q = Polynomial::<Monomial, GF101>::new(vec![GF101::new(1), GF101::new(1)]);
    println!("q: {}", q);
    let r = p / q;
    println!("r: {}", r);
    assert_eq!(r.coefficients, [GF101::new(1), GF101::new(1)]);
  }

  #[test]
  fn rem() {
    println!("poly_a: {}", poly_a());
    println!("poly_b: {}", poly_b());
    let q_ab = poly_a() % poly_b();
    assert_eq!(q_ab.coefficients, poly_a().coefficients);

    let q_ba = poly_b() % poly_a();
    assert_eq!(q_ba.coefficients, [GF101::new(11), GF101::new(41), GF101::new(71)]);
    println!("q_ba coefficients: {:?}", q_ba.coefficients);

    let p = Polynomial::<Monomial, GF101>::new(vec![GF101::new(1), GF101::new(2), GF101::new(1)]);
    println!("p: {}", p);
    let q = Polynomial::<Monomial, GF101>::new(vec![GF101::new(1), GF101::new(1)]);
    println!("q: {}", q);
    let r = p % q;
    println!("r: {}", r);
    assert_eq!(r.coefficients, [GF101::new(0)]);
  }
}
