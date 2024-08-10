//! Represents a multivariate polynomial over a finite field.
//!
//! This implementation uses a novel and highly efficient representation for multivariate polynomials.
//! Each term in the polynomial is represented as a key-value pair in a HashMap, where:
//! - The key is a BTreeMap mapping variable indices to their exponents.
//! - The value is the coefficient of the term.
//!
//! This representation offers several significant advantages:
//! 1. Space Efficiency: Only non-zero terms are stored, making it ideal for sparse polynomials.
//! 2. Fast Term Lookup: The use of BTreeMap for exponents allows for quick term identification and manipulation.
//! 3. Ordered Operations: BTreeMap's ordered nature facilitates efficient polynomial arithmetic.
//! 4. Memory Optimization: By using indices instead of full variable objects, we reduce memory usage.
//! 5. Flexible Degree Handling: This structure naturally accommodates polynomials of arbitrary degree.
//! 6. Efficient Iteration: Easy to iterate over terms, useful for various algorithms and transformations.
//!
//! While this representation may have a slight overhead for very small polynomials,
//! its benefits become increasingly apparent as the polynomial's complexity grows,
//! making it an excellent choice for a wide range of cryptographic and algebraic applications.

use std::collections::{HashMap, BTreeMap};
use std::hash::Hash;
use std::ops::{Add, Mul};
use itertools::Itertools;

use crate::algebra::field::FiniteField;
use super::*;
use super::{Monomial, Polynomial};

use std::ops::Sub;


/// Represents a multivariate polynomial over a finite field.
///
/// The polynomial is stored as a collection of terms, where each term is represented by:
/// - A `BTreeMap<usize, usize>` as the key, mapping variable indices to their exponents.
///   This allows for efficient storage and manipulation of sparse polynomials.
/// - An `F` value as the coefficient, where `F` is a finite field.
///
/// The use of `HashMap` for `terms` provides:
/// 1. O(1) average-case complexity for term lookup and insertion.
/// 2. Efficient storage for sparse polynomials, as only non-zero terms are stored.
///
/// The use of `BTreeMap` for exponents provides:
/// 1. Ordered storage of variable exponents, facilitating polynomial arithmetic.
/// 2. Efficient comparison and manipulation of terms.
/// 3. Memory efficiency by using indices instead of full variable objects.
///
/// This representation is particularly effective for large, sparse multivariate polynomials
/// commonly encountered in cryptographic and algebraic applications.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct MultivariatePolynomial<F: FiniteField> {
    terms: HashMap<BTreeMap<usize, usize>, F>,
}

impl<F: FiniteField> MultivariatePolynomial<F> {
    /// Constructs a new `MultivariatePolynomial` representing the zero polynomial.
    ///
    /// This function creates an empty `MultivariatePolynomial`, which is equivalent to the zero polynomial.
    /// The zero polynomial has no terms, and evaluates to zero for all inputs.
    pub fn new() -> Self {
        Self { terms: HashMap::new() }
    }


    /// Creates a new `MultivariatePolynomial` from a vector of `MultivariateTerm`s.
    ///
    /// This is the preferred way to create a multivariate polynomial, as it allows
    /// for a more intuitive representation of the polynomial's terms.
    ///
    /// # Arguments
    ///
    /// * `terms` - A vector of `MultivariateTerm`s representing the polynomial.
    ///
    /// # Returns
    ///
    /// A new `MultivariatePolynomial` instance.
    ///
    /// # Example
    ///
    /// ```
    /// use your_crate::{MultivariatePolynomial, MultivariateTerm, MultivariateVariable, PlutoBaseField};
    ///
    /// let poly = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    ///     MultivariateTerm::new(
    ///         vec![
    ///             MultivariateVariable { index: 0, exponent: 2 },
    ///             MultivariateVariable { index: 1, exponent: 1 }
    ///         ],
    ///         PlutoBaseField::new(3)
    ///     ),
    ///     MultivariateTerm::new(
    ///         vec![MultivariateVariable { index: 0, exponent: 1 }],
    ///         PlutoBaseField::new(2)
    ///     ),
    ///     MultivariateTerm::new(
    ///         vec![],
    ///         PlutoBaseField::new(1)
    ///     )
    /// ]);
    ///
    /// // This creates the polynomial: 3x_0^2*x_1 + 2x_0 + 1
    /// ```
    pub fn from_terms(terms: Vec<MultivariateTerm<F>>) -> Self {
        let mut poly = MultivariatePolynomial::new();
        for term in terms {
            let mut btree_map = BTreeMap::new();
            for var in term.variables {
                btree_map.insert(var.index, var.exponent);
            }
            poly.insert_term(btree_map, term.coefficient);
        }
        poly
    }

    fn insert_term(&mut self, exponents: BTreeMap<usize, usize>, coefficient: F) {
        if coefficient != F::ZERO {
            let entry = self.terms.entry(exponents.clone()).or_insert(F::ZERO);
            *entry += coefficient;
            if *entry == F::ZERO {
                self.terms.remove(&exponents);
            }
        }
    }

    /// Returns the coefficient of the term with the given exponents.
    ///
    /// # Arguments
    ///
    /// * `exponents` - A `BTreeMap` where the keys are variable indices and the values are their exponents.
    ///
    /// # Returns
    ///
    /// * `Some(&F)` if a term with the given exponents exists in the polynomial, where `F` is the coefficient.
    /// * `None` if no term with the given exponents exists in the polynomial.
    ///
    /// # Example
    ///
    /// ```
    /// use std::collections::BTreeMap;
    /// use your_crate::{MultivariatePolynomial, PlutoBaseField};
    ///
    /// let poly = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    ///     // ... (terms as in the previous example)
    /// ]);
    ///
    /// let mut exponents = BTreeMap::new();
    /// exponents.insert(0, 2);
    /// exponents.insert(1, 1);
    ///
    /// assert_eq!(poly.coefficient(&exponents), Some(&PlutoBaseField::new(3)));
    /// ```
    pub fn coefficient(&self, exponents: &BTreeMap<usize, usize>) -> Option<&F> {
        self.terms.get(exponents)
    }

    /// Evaluates the multivariate polynomial at the given points.
    ///
    /// # Arguments
    ///
    /// * `points` - A slice of tuples where each tuple contains:
    ///   - The index of the variable (usize)
    ///   - The value to evaluate the variable at (F)
    ///
    /// # Returns
    ///
    /// * The result of evaluating the polynomial (F)
    ///
    /// # Example
    ///
    /// ```
    /// use your_crate::{MultivariatePolynomial, PlutoBaseField};
    ///
    /// let poly = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    ///     // x^2 + 2xy + 3z
    ///     // ... (terms definition)
    /// ]);
    ///
    /// let points = vec![(0, PlutoBaseField::new(2)), (1, PlutoBaseField::new(3)), (2, PlutoBaseField::new(1))];
    /// let result = poly.evaluate(&points);
    /// // result will be the evaluation of x^2 + 2xy + 3z at x=2, y=3, z=1
    /// ```
    pub fn evaluate(&self, points: &[(usize, F)]) -> F {
        self.terms.iter().map(|(exponents, coeff)| {
            let term_value = exponents.iter().map(|(&var, &exp)| {
                points.iter()
                    .find(|&&(v, _)| v == var)
                    .map(|&(_, value)| value.pow(exp))
                    .unwrap_or(F::ONE)
            }).product::<F>();
            *coeff * term_value
        }).sum()
    }

    /// Applies the given variable assignments to the polynomial, reducing its degree.
    ///
    /// This method substitutes the specified variables with their corresponding values,
    /// effectively reducing the polynomial's degree for those variables. The resulting
    /// polynomial will have fewer variables if any were fully substituted.
    ///
    /// # Arguments
    ///
    /// * `variables` - A slice of tuples, where each tuple contains:
    ///   - The index of the variable to substitute (usize)
    ///   - The value to substitute for that variable (F)
    ///
    /// # Returns
    ///
    /// A new `MultivariatePolynomial<F>` with the specified variables substituted.
    ///
    /// # Example
    ///
    /// ```
    /// use your_crate::{MultivariatePolynomial, PlutoBaseField};
    ///
    /// let poly = MultivariatePolynomial::<PlutoBaseField>::from_terms(vec![
    ///     // x^2y + 3xyz + 2z
    ///     // ... (terms definition)
    /// ]);
    ///
    /// let assignments = vec![(1, PlutoBaseField::new(2))]; // y = 2
    /// let reduced_poly = poly.apply_variables(&assignments);
    /// // The resulting polynomial will be of the form: 2x^2 + 6xz + 2z
    /// ```
    pub fn apply_variables(&self, variables: &[(usize, F)]) -> Self {
        let mut result = MultivariatePolynomial::new();
        
        for (exponents, coeff) in &self.terms {
            let mut new_exponents = exponents.clone();
            let mut new_coeff = *coeff;
            
            for &(var, value) in variables {
                if let Some(exp) = new_exponents.get(&var) {
                    new_coeff *= value.pow(*exp);
                    new_exponents.remove(&var);
                }
            }
            
            if !new_exponents.is_empty() {
                result.insert_term(new_exponents, new_coeff);
            } else {
                result.insert_term(BTreeMap::new(), new_coeff);
            }
        }
        
        result
    }
    
    
    /// Calculates the total degree of the multivariate polynomial.
    ///
    /// The total degree of a multivariate polynomial is the maximum sum of exponents
    /// across all terms in the polynomial.
    ///
    /// # Returns
    ///
    /// * `usize` - The total degree of the polynomial.
    ///
    /// # Example
    ///
    /// ```
    /// use your_crate::MultivariatePolynomial;
    /// use your_crate::FiniteField;
    ///
    /// let poly = MultivariatePolynomial::<F>::from_terms(vec![
    ///     // x^2y + 3xyz^2 + 2z
    ///     // ... (terms definition)
    /// ]);
    ///
    /// assert_eq!(poly.degree(), 4); // The term xyz^2 has the highest total degree of 4
    /// ```
    pub fn degree(&self) -> usize {
        self.terms.keys()
            .map(|exponents| exponents.values().sum::<usize>())
            .max()
            .unwrap_or(0)
    }

    /// Returns a vector of all variables present in the polynomial.
    ///
    /// This method collects all unique variables (represented by their indices)
    /// that appear in any term of the polynomial.
    ///
    /// # Returns
    ///
    /// * `Vec<usize>` - A vector containing the indices of all variables in the polynomial.
    ///
    /// # Example
    ///
    /// ```
    /// use your_crate::MultivariatePolynomial;
    /// use your_crate::FiniteField;
    ///
    /// let poly = MultivariatePolynomial::<F>::from_terms(vec![
    ///     // x^2y + 3xyz^2 + 2z
    ///     // ... (terms definition)
    /// ]);
    ///
    /// let vars = poly.variables();
    /// assert_eq!(vars, vec![0, 1, 2]); // Assuming x, y, z are represented by 0, 1, 2 respectively
    /// ```
    pub fn variables(&self) -> Vec<usize> {
        self.terms.keys()
            .flat_map(|exponents| exponents.keys().cloned())
            .collect::<std::collections::HashSet<_>>()
            .into_iter()
            .collect()
    }
}

impl<F: FiniteField> Add for MultivariatePolynomial<F> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        for (exponents, coeff) in rhs.terms {
            self.insert_term(exponents, coeff);
        }
        self
    }
}

impl<F: FiniteField> Sub for MultivariatePolynomial<F> {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        for (exponents, coeff) in rhs.terms {
            // Negate the coefficient and insert
            self.insert_term(exponents, -coeff);
        }
        self
    }
}

impl<F: FiniteField> Mul for MultivariatePolynomial<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut result = MultivariatePolynomial::new();
        for (exp1, coeff1) in &self.terms {
            for (exp2, coeff2) in &rhs.terms {
                let mut new_exp = exp1.clone();
                for (&var, &exp) in exp2 {
                    *new_exp.entry(var).or_insert(0) += exp;
                }
                result.insert_term(new_exp, *coeff1 * *coeff2);
            }
        }
        result
    }
}

impl<F: FiniteField + Display> Display for MultivariatePolynomial<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for (exponents, coeff) in self.terms.iter().sorted_by(|(a_exp, _), (b_exp, _)| {
            a_exp.iter()
                .zip(b_exp.iter())
                .find(|((a_var, a_pow), (b_var, b_pow))| {
                    a_var.cmp(b_var).then_with(|| b_pow.cmp(a_pow)).is_ne()
                })
                .map_or(std::cmp::Ordering::Equal, |(_, _)| std::cmp::Ordering::Less)
        }) {
            if !first {
                write!(f, " + ")?;
            }
            first = false;

            if *coeff != F::ONE || exponents.is_empty() {
                write!(f, "{}", coeff)?;
            }

            let mut first_var = true;
            for (&var, &exp) in exponents {
                if exp > 0 {
                    if !first_var || *coeff != F::ONE {
                        write!(f, "*")?;
                    }
                    write!(f, "x_{}", var)?;
                    if exp > 1 {
                        write!(f, "^{}", exp)?;
                    }
                    first_var = false;
                }
            }
        }

        if first {
            write!(f, "0")?;
        }

        Ok(())
    }
}

// Implement From for univariate polynomials
impl<F: FiniteField, const D: usize> From<Polynomial<Monomial, F, D>> for MultivariatePolynomial<F> {
    fn from(poly: Polynomial<Monomial, F, D>) -> Self {
        let mut result = MultivariatePolynomial::new();
        for (i, &coeff) in poly.coefficients.iter().enumerate() {
            if coeff != F::ZERO {
                let mut exponents = BTreeMap::new();
                exponents.insert(0, i);
                result.insert_term(exponents, coeff);
            }
        }
        result
    }
}

// Extend Polynomial to support conversion to multivariate
impl<F: FiniteField, const D: usize> Polynomial<Monomial, F, D> {
    /// Converts a univariate polynomial to a multivariate polynomial.
    ///
    /// This method transforms the current univariate polynomial into a multivariate polynomial
    /// where all terms use the same variable, specified by `variable_index`.
    ///
    /// # Arguments
    ///
    /// * `variable_index` - The index of the variable to use in the resulting multivariate polynomial.
    ///
    /// # Returns
    ///
    /// A `MultivariatePolynomial<F>` equivalent to the original univariate polynomial.
    ///
    /// # Example
    ///
    /// ```
    /// let univariate = Polynomial::new([F::ONE, F::TWO, F::THREE]); // x^2 + 2x + 1
    /// let multivariate = univariate.to_multivariate(0);
    /// // Result: x_0^2 + 2*x_0 + 1
    /// ```
    pub fn to_multivariate(self, variable_index: usize) -> MultivariatePolynomial<F> {
        let mut result = MultivariatePolynomial::new();
        for (i, &coeff) in self.coefficients.iter().enumerate() {
            if coeff != F::ZERO {
                let mut exponents = BTreeMap::new();
                exponents.insert(variable_index, i);
                result.insert_term(exponents, coeff);
            }
        }
        result
    }
}


/// Represents a variable with an exponent in a multivariate polynomial.
/// Each variable is uniquely identified by its index and has an associated exponent.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MultivariateVariable {
    /// The unique identifier for the variable.
    /// This index distinguishes one variable from another in the polynomial.
    pub index: usize,

    /// The power to which the variable is raised.
    /// For example, if exponent is 2, it represents x^2 for the variable x.
    pub exponent: usize,
}

impl MultivariateVariable {
    /// Creates a new multivariate variable with the given index and exponent.
    pub fn new(index: usize, exponent: usize) -> Self {
        MultivariateVariable { index, exponent }
    }
}

/// Represents a term in a multivariate polynomial.
/// 
/// # Fields
/// 
/// * `variables` - A vector of `MultivariateVariable`s representing the variables in this term.
/// * `coefficient` - The coefficient of this term, represented as a finite field element.
#[derive(PartialEq, Eq)]
pub struct MultivariateTerm<F: FiniteField> {
    /// A vector of `MultivariateVariable`s representing the variables in this term.
    /// Each `MultivariateVariable` contains an index and an exponent.
    pub variables: Vec<MultivariateVariable>,

    /// The coefficient of this term, represented as a finite field element.
    /// This value multiplies the product of the variables in the term.
    pub coefficient: F,
}

/// Represents a term in a multivariate polynomial.
/// A term consists of a coefficient and a collection of variables with their exponents.
impl<F: FiniteField> MultivariateTerm<F> {
    /// Creates a new multivariate term with the given variables and coefficient.
    pub fn new(variables: Vec<MultivariateVariable>, coefficient: F) -> Self {
        MultivariateTerm { variables, coefficient }
    }
}
