<h1 align="center">
  ronkathon
</h1>

<p align="center">
  ronkathon
</p>

<div align="center">
  <a href="https://github.com/pluto/ronkathon/actions">
    <!-- ![](https://github.com/pluto/ronkathon/actions/workflows/ci.yml/badge.svg) -->
    <img src="https://github.com/pluto/ronkathon/actions/workflows/ci.yml/badge.svg" />
  </a>
  <!-- [![crates.io](https://img.shields.io/crates/v/ronkathon.svg)](https://crates.io/crates/ronkathon) -->
  <!-- [![Documentation](https://docs.rs/ronkathon/badge.svg)](https://docs.rs/ronkathon) -->
  </div>

## Overview
Ronkathon is a rust implementation of a collection of cryptographic primitives. It is inspired by the common python plonkathon repository, and plonk-by-hand. We use the same curve and field as plonk-by-hand (not secure), and are working towards building everything from scratch to understand everything from first principles.

## Primitives
- [Fields and Their Extensions](src/fields/README.md)
- [Curves and Their Pairings](src/curves/README.md)
- [Polynomials](src/polynomials/mod.rs)
- [KZG Commitments](src/kzg/README.md)
- [Reed-Solomon Codes](src/codes/README.md)
- [Tiny ECDSA](src/ecdsa.rs)
- [RSA](src/tiny_rsa/README.md)
- [Sha256 Hash](src/hash/README.md)
- [Merkle Proofs](src/tree/README.md)
- [Poseidon Hash](src/hashes/poseidon/README.md)

## In Progress
- [ ] Edwards curve Signatures (EdDSA)

## Resources

We have found the following resources helpful in understanding the foundational mathematics behind this implementation. After going through these, you should be able to understand the codebase

### Theoretic Resources
- [Plonk by Hand P1](https://research.metastate.dev/plonk-by-hand-part-1/)
- [Plonk by Hand P2](https://research.metastate.dev/plonk-by-hand-part-2-the-proof/)
### Code Refrences
- [Plonkathon](https://github.com/0xPARC/plonkathon/blob/main/README.md)
- [Plonky3](https://github.com/Plonky3/Plonky3)
- [py_pairing](https://github.com/ethereum/py_pairing/tree/master)
- [arkworks](https://github.com/arkworks-rs)


## Math
To see computations used in the background, go to the `math/` directory.
From there, you can run the `.sage` files in a SageMath environment.
In particular, the `math/field.sage` computes roots of unity in the `PlutoField` which is of size 101. To install sage on your machine, follow the instructions [here](https://doc.sagemath.org/html/en/installation/index.html). If you are on a Mac, you can install it via homebrew with `brew install --cask sage`.

## License
Licensed under your option of either:
- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

## Contribution
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
