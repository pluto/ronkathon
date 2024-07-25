# Algebra

[Groups](https://en.wikipedia.org/wiki/Group_(mathematics)) $G$ are algebraic structures which are set and has a binary operation $\oplus$ that combines two elements $a, b$ of the set to produce a third element $a\oplus b$ in the set.
The operation is said to have following properties:
1. Closure: $a\oplus b=c\in G$
2. Associative: $(a\oplus b)\oplus c = a\oplus(b\oplus c)$
3. Existence of Identity element: $a\oplus 0 = 0\oplus a = a$
4. Existence of inverse element for every element of the set: $a\oplus b=0$
5. Commutativity: Groups which satisfy an additional property: *commutativity* on the set of
   elements are known as **Abelian groups**.

[Rings](https://en.wikipedia.org/wiki/Ring_(mathematics)) are algebraic structures with two binary operations $R(\oplus, \cdot)$ satisfying the following properties:
1. Abelian group under $\oplus$.
2. Monoid under $\cdot$.
3. Distributive with respect to $\oplus$.

[Finite fields](https://en.wikipedia.org/wiki/Finite_field) are instrumental in cryptographic systems.
They are used in elliptic curve cryptography, RSA, and many other cryptographic systems.
This module provides a generic implementation of finite fields via two traits and two structs.
It is designed to be easy to use and understand, and to be flexible enough to extend yourself.

## Constant (Compile Time) Implementations
Note that traits defined in this module are tagged with `#[const_trait]` which implies that each method and associated constant is implemented at compile time.
This is done purposefully as it allows for generic implementations of these fields to be constructed when you compile `ronkathon` rather than computed at runtime.
In principle, this means the code runs faster, but will compile slower, but the tradeoff is that the cryptographic system is faster and extensible.