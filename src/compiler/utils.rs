//! Utilities for parsing

/// Checks whether a variable name is valid.
/// - len > 0
/// - chars are alphanumeric
/// - 1st element is not a number
pub(crate) fn is_valid_var_name(name: &str) -> bool {
  !name.is_empty()
    && name.chars().all(char::is_alphanumeric)
    && !(48u8..=57u8).contains(&name.as_bytes()[0])
}

/// returns product key required for coefficient mapping in plonk's multiplication gate variable.
/// split `a` and `b` by `*`, sort and join by `*`.
pub(crate) fn get_product_key(a: &str, b: &str) -> String {
  // TODO: might be a better alternative here
  match (a, b) {
    ("$constant", "$constant") => String::from("$constant"),
    ("$constant", b) => String::from(b),
    (a, "$constant") => String::from(a),
    (a, b) => {
      let mut a_star: Vec<&str> = a.split('*').collect();
      a_star.append(&mut b.split('*').collect());

      a_star.sort();
      a_star.join("*")
    },
  }
}

#[cfg(test)]
mod tests {
  use rstest::rstest;

  use super::*;

  #[rstest]
  #[case("a", "b", "a*b")]
  #[case("a*b", "c", "a*b*c")]
  #[case("a*c", "d*b", "a*b*c*d")]
  #[case("$constant", "$constant", "$constant")]
  #[case("$constant", "a", "a")]
  #[case("a", "$constant", "a")]
  fn product_key(#[case] a: &str, #[case] b: &str, #[case] expected: &str) {
    assert_eq!(get_product_key(a, b), expected);
  }

  #[rstest]
  #[case("a", true)]
  #[case("abcd", true)]
  #[case("", false)]
  #[case("1", false)]
  #[case("1a", false)]
  fn valid_var_name(#[case] var: &str, #[case] expected: bool) {
    assert_eq!(is_valid_var_name(var), expected);
  }
}
