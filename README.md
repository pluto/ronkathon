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
Ronkathon is an implementation of plonkish KZG-based proofs. It is inspired by the common python plonkathon repository, and plonk-by-hand. We use the same curve and field as plonk-by-hand (not secure), and are working towards building everything from scratch to understand everything from first principles.

## Resources

We have found the following resources helpful in understanding the foundational mathematics behind this implementation. After going through these, you should be able to understand the codebase. In order it is recommended to understand:
- Finite Fields
- Extension Fields
- Elliptic Curves over Fields and Extension Fields
- Embedding degree
- Polynomials
- FFTs
- Pairings

In order to set up the for KZG proofs you need two elliptic curve groups that make up a pairing. (most of our constants are from plonk-by-hand) The construction of pairing friendly groups is done by: 

1) Choosing a Finite field of prime order: We have chosen $p = 101$
2) Choosing an elliptic curve over the field: We have chosen: $y^2=x^3+3$
3) Selecting the generator point for the first curve: We chose $(1,2)$
4) find the embedding degree of the curve: the embedding degree here is $2$
the embedding degree is the smallest number $k$ such that $r | p^k - 1$ where $r$ is the order of the curve: $17$
5) Construct a field extension from the first field such that $f_{p^2}$ is a field extension of $f_p$, we extend with $x^2 + 2$ which is irreducible in $F_{101}$
6) Now we can construct pairing friendly curve over the field extension and get a generator point for the second curve: $g2 = (31, 36x)$
7) Construct the structured refrence string SRS with g1 and g2. 

TODO: Talk about the proof construction that uses the SRS, how big the SRS needs to be and the pairing check at the end. 


### Theoretic Resources
- [A gentle introduction to Fast Fourier Transforms over Finite Fields](https://vitalik.eth.limo/general/2019/05/12/fft.html)
- [Introduction to Pairings](https://vitalik.eth.limo/general/2017/01/14/exploring_ecp.html)
- [KZG introduction by dankrad](https://dankradfeist.de/ethereum/2020/06/16/kate-polynomial-commitments.html)
- [Pairings in depth](https://static1.squarespace.com/static/5fdbb09f31d71c1227082339/t/5ff394720493bd28278889c6/1609798774687/PairingsForBeginners.pdf)
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
