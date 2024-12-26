<h1 align="center">
  ronkathon
</h1>
<div align="center">
  <a href="https://github.com/pluto/ronkathon/graphs/contributors">
    <img src="https://img.shields.io/github/contributors/pluto/ronkathon?style=flat-square&logo=github&logoColor=8b949e&labelColor=282f3b&color=32c955" alt="Contributors" />
  </a>
  <a href="https://github.com/pluto/ronkathon/actions/workflows/test.yaml">
    <img src="https://img.shields.io/badge/tests-passing-32c955?style=flat-square&logo=github-actions&logoColor=8b949e&labelColor=282f3b" alt="Tests" />
  </a>
  <a href="https://github.com/pluto/ronkathon/actions/workflows/lint.yaml">
    <img src="https://img.shields.io/badge/lint-passing-32c955?style=flat-square&logo=github-actions&logoColor=8b949e&labelColor=282f3b" alt="Lint" />
  </a>
</div>

## Overview

Ronkathon is a collection of cryptographic primitives implemented in Rust. It is inspired by the [python plonkathon repository](https://github.com/0xPARC/plonkathon) and [plonk-by-hand](https://research.metastate.dev/plonk-by-hand-part-1/). We use the same curve and field as plonk-by-hand (which is not secure) and the goal of this repository is to work towards building everything from scratch to understand everything from first principles.

## Multivariate polynomials and sum-check

This project implements the sum-check protocol for multivariate polynomials over finite fields. The sum-check protocol is an interactive proof system where a prover convinces a verifier of the sum of a multivariate polynomial over a boolean hypercube. This implementation includes:

- A `MultiVarPolynomial` struct which represents a multivariate polynomial
- A `SumCheckProver` for generating proofs
- A `SumCheckVerifier` for verifying proofs
- A `SumCheck` struct that encapsulates the entire protocol.

You can use:

`cargo run --example sumcheck_ex`

to run example code.

## Primitives

- [Finite Group](src/field/group.rs)
- [Fields and Their Extensions](src/field/README.md)
  - [Binary Fields](src/field/binary_towers/README.md)
- [Curves and Their Pairings](src/curve/README.md)
- [Polynomials](src/polynomial/mod.rs)
- [KZG Commitments](src/kzg/README.md)
- [Reed-Solomon Codes](src/codes/README.md)
- [Merkle Proofs](src/tree/README.md)
- [DSL](src/compiler/README.md)

### Signatures

- [Tiny ECDSA](src/ecdsa.rs)

### Encryption

####  Asymmetric
- [RSA](src/encryption/asymmetric/rsa/README.md)

#### Symmetric

- **Ciphers:**
    + [DES](src/encryption/symmetric/des/README.md)
    + [AES](src/encryption/symmetric/aes/README.md)
    + [ChaCha](src/encryption/symmetric/chacha/README.md)

- [**Modes of Operation**](src/encryption/symmetric/modes/README.md)
    + ECB, CBC, CTR, GCM

### Hash

- [Sha256 Hash](src/hashes/README.md)
- [Poseidon Hash](src/hashes/poseidon/README.md)

## In Progress

- [ ] Edwards curve Signatures (EdDSA)

## Resources

We have found the following resources helpful in understanding the foundational mathematics behind this implementation. After going through these, you should be able to understand the codebase

### Theoretic Resources

- [Plonk by Hand P1](https://research.metastate.dev/plonk-by-hand-part-1/)
- [Plonk by Hand P2](https://research.metastate.dev/plonk-by-hand-part-2-the-proof/)
- [Plonk by Hand P3](https://research.metastate.dev/plonk-by-hand-part-3-verification/)

### Code References

- [Plonkathon](https://github.com/0xPARC/plonkathon/blob/main/README.md)
- [Plonky3](https://github.com/Plonky3/Plonky3)
- [py_pairing](https://github.com/ethereum/py_pairing/tree/master)
- [arkworks](https://github.com/arkworks-rs)

## Math

To see computations used in the background, go to the `math/` directory.
From there, you can run the `.sage` files in a SageMath environment.
In particular, the `math/field.sage` computes roots of unity in the `PlutoField` which is of size 101. To install sage on your machine, follow the instructions [here](https://doc.sagemath.org/html/en/installation/index.html). If you are on a Mac, you can install it via homebrew with `brew install --cask sage`.

## License

Licensed under the Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)

## Contributing

We welcome contributions to our open-source projects. If you want to contribute or follow along with contributor discussions, join our [main Telegram channel](https://t.me/pluto_xyz/1) to chat about Pluto's development.

Our contributor guidelines can be found at [CONTRIBUTING.md](https://github.com/pluto/.github/blob/main/profile/CONTRIBUTING.md). A good starting point is issues labelled 'bounty' in our repositories.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be licensed as above, without any additional terms or conditions.
