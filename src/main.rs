use ronkathon::field::gf_101::GF101;

fn main() {
  let f = GF101::new(1);
  println!("hello field={:?}", f);

  let g = generator(101);
  println!("generator={:?}", g);
}

// algorithm to compute primitive element of field (multiplicative generator)
fn generator(p: u32) -> i32 {
  let mut fact = Vec::new();
  let phi = p - 1;
  let mut n = phi;
  let mut i = 2;
  while i * i <= n {
    if n % i == 0 {
      fact.push(i);
      while n % i == 0 {
        n /= i;
      }
    }
    i += 1;
  }
  if n > 1 {
    fact.push(n);
  }

  for res in 2..=p {
    let mut ok = true;
    for &f in &fact {
      ok &= powmod(res, phi / f, p) != 1;
      if !ok {
        break;
      }
    }
    if ok {
      return res as i32;
    }
  }
  -1
}

fn powmod(base: u32, exponent: u32, modulus: u32) -> u32 {
  let mut base = base as u64;
  let mut exponent = exponent;
  let modulus = modulus as u64;
  let mut result = 1;
  base %= modulus;
  while exponent > 0 {
    if exponent % 2 == 1 {
      result = (result * base) % modulus;
    }
    base = (base * base) % modulus;
    exponent >>= 1;
  }
  result as u32
}
