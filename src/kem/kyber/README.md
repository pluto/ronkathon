# Module Lattice Based KEM (FIPS 203)

## ToC
- [ ] Intrduction
- [ ] Preliminaries
- [ ] Parameters
- [ ] Encryption
- [ ] KEM
- [ ] Optimisation
- [ ] Performance
- [ ] Security


## Introduction

> [!NOTE]
> Implementation and terminilogy follows FIPS 203 that formalises PQ-KEM standard for the internet.

ML-KEM is based on Module Learning with Errors problems introduced by [Reg05][Reg05].

## Preliminaries

## Implementation Details
- Polynomial Rings
  - representation
  - Arithmetic with Polynomials
- Matrices and Vectors
  - representation
  - Arithmetic
- cryptographic functions
  - SHA3-256, SHA3-512
  - SHAKE128, SHAKE256
  - PRF: $\textsf{PRF}_{\eta}(s,b):=\text{SHAKE256}(s\|b,8\cdot 64 \cdot \eta)$
  - Hash function:
    - $H: H(s) := \text{SHA3-256}(s)$, where $s\in \mathbb{B}^*$
    - $J: J(s) := \text{SHAKE256}(s,8\cdot 32)$, where $s\in \mathbb{B}^*$
    - $G:\ G(c \in \mathbb{B}^*) := \text{SHA3-512}(c) \in \mathbb{B}^{32}\times\mathbb{B}^{32}$
  - XOF: SHAKE128
- General Functions:
  - BitsToBytes, BytesToBits
  - Compression, Decompression
  - ByteEncode, ByteDecode
- Sampling algorithms:
  - SampleNTT
- NTT, RevNTT
- MultiplyNTT
- BaseCaseMultiply

## NTT: Number-Theroretic Transform

- Special case of FFT performed over $\mathbb{Z}_q^*$.
- Most computationally intensive operation in encryption scheme is the multiplication of polynomials in $\mathcal{R}_{q,f}$ that is $\mathcal{O}(n^2)$, where $n$ is the degree of the polynomial. NTT allows to perform this in $\mathcal{O}(n\log n)$.
- Polynomial: $\mathbb{Z}_q[X]/(X^d+\alpha)$, where $d=2^k$ and $-\alpha$ is perfect square of $d\in\mathbb{Z}_q$
  - $X^d+\alpha\equiv(X^{d/2}-r)(X^{d/2}+r)\mod q$
- Using, Chinese Remainder Theorem, $ab\in\mathbb{Z}_q/(X^d+\alpha)$ can be written as $ab \mod (X^{d/2}+r),\ ab \mod (X^{d/2}-r)$, and can be converted back to $\mod (X^d+\alpha)$.
- Doing this recursively, asymptotic complexity of the algorithm turns out to be $d\log d$

## Parameters
- $q=3329=2^8+1$
- $f=X^{256}+1$
- $k,\eta_1,\eta_2,d_u,d_v$ vary according to parameter sets.

|            | k   | $\eta_1$ | $\eta_2$ | $d_u$ | $d_v$ | decryption error | pk size | ciphertext size |
| ---------- | --- | -------- | -------- | ----- | ----- | ---------------- | ------- | --------------- |
| Kyber-512  | 3   | 3        | 2        | 10    | 4     | $2^{−139}$       | 800B    | 768B            |
| Kyber-768  | 4   | 2        | 2        | 10    | 4     | $2^{−164}$       | 1184B   | 1088B           |
| Kyber-1024 | 5   | 2        | 2        | 11    | 5     | $2^{−174}$       | 1568B   | 1568B           |

## CPA-secure Encryption Scheme
1. $\text{KeyGen}$
2.

## TODO

- [ ] FIPS 202: SHA3-{256,512}, SHAKE{128,256}
- [ ] Rings, Polynomial Rings
  - [ ] arithmetic for rings
  - [ ]

## References
- [Module-Lattice-Based Key-Encapsulation Mechanism Standard](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.pdf)
- [RustCrypto/KEMs](https://github.com/RustCrypto/KEMs): const functions inspiration

[Reg05]: <https://cims.nyu.edu/~regev/papers/lwesurvey.pdf>