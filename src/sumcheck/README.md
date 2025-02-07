# Multivariate Polynomials and Sum-Check  

This project implements the **sum-check protocol** for multivariate polynomials over finite fields. The sum-check protocol is an **interactive proof system** where a **prover** convinces a **verifier** of the sum of a multivariate polynomial over a **boolean hypercube**.  

## Features  

This implementation includes:  

- **`MultiVarPolynomial`** – a struct that represents a multivariate polynomial.  
- **`SumCheckProver`** – responsible for generating proofs.  
- **`SumCheckVerifier`** – responsible for verifying proofs.  
- **`SumCheck`** – a struct that encapsulates the entire protocol.  

## Why Sum-Check?  

The sum-check protocol is widely used in **zero-knowledge proofs** (ZKPs), **verifiable computation**, and other cryptographic applications. It allows a verifier to check the sum of a polynomial over an exponential-sized space with only a logarithmic number of interactions. This protocol is a core building block in zk-SNARKs and other advanced cryptographic techniques.  

## Installation and Usage  

Ensure you have **Rust** installed. Then, you can run the example code using:  

```sh
cargo run --example sumcheck_ex
```  

If needed, install Rust and Cargo by following the instructions at [rust-lang.org](https://www.rust-lang.org/).  
