# Elliptic Curve Cryptography

Elliptic curve cryptography takes advantage of the intractability of the elliptic curve discrete logarithm problem.

Let $E$ be an elliptic curve defined over a Galois (finite) field $\mathbb{F}_q$. Point addition forms a cyclic group
on $E(\mathbb{F}_q)$ with a generator point $G \in E(\mathbb{F}_q)$ and a point at infinite $\mathcal{O}$ such that:

$$
\forall P, Q \in E(\mathbb{F}_q) : P + Q = R \in E(\mathbb{F}_q)
\forall P \in E(\mathbb{F}_q) : P + \mathcal{O} = P
\forall P \in E(\mathbb{F}_q) : P + (-P) = \mathcal{O}
$$

Scalar multiplication is defined as iterative point addition such that:

$$
\forall P \in E(\mathbb{F}_q), k \in \mathbb{Z} : k \times P = P_k \in E(\mathbb{F}_q)
\forall P_k \in E(\mathbb{F}_q), \exists k \in \mathbb{Z} : k \times G = P_k
$$

## Application

The discrete logarithm problem and algebraic structure of elliptic curve point addition and scalar multiplication
allows for public key cryptography schemes such as digital signatures
([ECDSA](https://en.wikipedia.org/wiki/Elliptic_Curve_Digital_Signature_Algorithm)) and key exchanges
([ECDH](https://en.wikipedia.org/wiki/Elliptic-curve_Diffie%E2%80%93Hellman)).
