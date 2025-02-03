## Multivariate polynomials and sum-check

This project implements the sum-check protocol for multivariate polynomials over finite fields. The sum-check protocol is an interactive proof system where a prover convinces a verifier of the sum of a multivariate polynomial over a boolean hypercube. This implementation includes:

- A `MultiVarPolynomial` struct which represents a multivariate polynomial
- A `SumCheckProver` for generating proofs
- A `SumCheckVerifier` for verifying proofs
- A `SumCheck` struct that encapsulates the entire protocol.

You can use:

`cargo run --example sumcheck_ex`

to run example code.