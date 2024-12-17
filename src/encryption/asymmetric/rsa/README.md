# Tiny RSA

RSA was one of the first asymmetric cryptographic primitives in which the key used for encryption is different from the key used for decryption.
The security of RSA is based on the difficulty of factoring large integers.

## Key Generation

1. Consider two large prime numbers $p$ and $q$.
2. Calculate $n = p \times q$
3. Calculate $\phi(n) = (p-1) \times (q-1)$
4. Choose $e$ such that $1 < e < \phi(n)$ and $e$ is coprime to $\phi(n)$, or in other words $gcd(e, \phi(n)) = 1$
5. Calculate $d$ such that $d \times e \equiv 1 \mod \phi(n)$

## Keys
Private Key = $(d, n)$
Public Key = $(e, n)$

## Encryption
- $c = m^e \mod n$

## Decryption
- $m = c^d \mod n$

See the examples in the tests.rs file

## Security Assumptions
The security of RSA relies on the assumption that it is computationally infeasible to factor large composite numbers into their prime factors, known as the factoring assumption. This difficulty underpins the RSA problem, which involves computing eth roots modulo  n  without the private key.
