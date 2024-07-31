# Algebra

[Groups](https://en.wikipedia.org/wiki/Group_(mathematics)) $G$ are algebraic structures which are set and has a binary operation $\cdot$ that combines two elements $a, b$ of the set to produce a third element $a\cdot b$ in the set.
The operation is said to have following properties:
1. Closure: $a\cdot b=c\in G$
2. Associative: $(a\cdot b)\cdot c = a\cdot(b\cdot c)$
3. Existence of Identity element: $a\cdot 0 = 0\cdot a = a$
4. Existence of inverse element for every element of the set: $a\cdot b=0$
5. Commutativity: Groups which satisfy an additional property: *commutativity* on the set of
   elements are known as **Abelian groups**, $a\cdot b=b\cdot a$.

Examples:
- $Z$ is a group under addition defined as $(Z,+)$
- $(Z/nZ)^{\times}$ is a finite group under multiplication
- Equilateral triangles for a non-abelian group of order 6 under symmetry.
- Invertible $n\times n$ form a non-abelian group under multiplication.

[Rings](https://en.wikipedia.org/wiki/Ring_(mathematics)) are algebraic structures with two binary operations $R(+, \cdot)$ satisfying the following properties:
1. Abelian group under +
2. Monoid under $\cdot$
3. Distributive with respect to $\cdot$

Examples:
- $Z/nZ$ form a ring
- a polynomial with integer coefficients: $Z[x]$ satisfy ring axioms

[Fields](https://en.wikipedia.org/wiki/Field_(mathematics)) are algebraic structures with two binary operations $F(+,\cdot)$ such that:
- Abelian group under $+$
- Non-zero numbers $F-\{0\}$ form abelian group under $\cdot$
- Multiplicative distribution over $+$

> Fields can also be defined as commutative ring $(R,+,\cdot)$ with existence of inverse under $\cdot$. Thus, every Field can be classified as Ring.

Examples:
- $\mathbb{Q,R,C}$, i.e. set of rational, real and complex numbers are all Fields.
- $\mathbb{Z}$ is **not** a field.
- $Z/nZ$ form a finite field under modulo addition and multiplication.

[Finite fields](https://en.wikipedia.org/wiki/Finite_field) are field with a finite order and are instrumental in cryptographic systems. They are used in elliptic curve cryptography, RSA, and many other cryptographic systems.
This module provides a generic implementation of finite fields via two traits and two structs.
It is designed to be easy to use and understand, and to be flexible enough to extend yourself.

## Constant (Compile Time) Implementations
Note that traits defined in this module are tagged with `#[const_trait]` which implies that each method and associated constant is implemented at compile time.
This is done purposefully as it allows for generic implementations of these fields to be constructed when you compile `ronkathon` rather than computed at runtime.
In principle, this means the code runs faster, but will compile slower, but the tradeoff is that the cryptographic system is faster and extensible.