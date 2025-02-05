# Diffie-Hellman Key Exchanges

## What is Diffie-Hellman?

The Diffie-Hellman key exchange protocol, named after Whitfield Diffie and Martin Hellman, is a protocol for two parties to create a shared secret over a public channel without revealing information about the key.

The exchange is made possible by using commutativity in finite cyclic groups, particularly with elliptic curve cyclic groups. That is to say, given a common generator point on an elliptic curve over a finite field $G \in E(\mathbb{F}_p)$, two parties, Alice and Bob may choose secrets, $a \in \mathbb{F}_p$ and $b \in \mathbb{F}_p$ respectively, compute their respective elliptic curve points $[a]G = A \in E(\mathbb{F}_p)$ and $[b]G = B \in E(\mathbb{F}_p)$ (again respectively), and exchange these on a public channel. Finally, they may perform the elliptic curve point arithmetic on their received points with their secrets as follows.

Alice:

$$[a](B) = [a]([b]G) = [ab]G$$

Bob:

$$[b](A) = [b]([a]G) = [ba]G$$

Finally:

$$[ba]G = [ab]G$$

As such, Alice and Bob have computed a shared secret $[ab]G \in E(\mathbb{F}_p)$ by sharing only $B$ and $A$ over a public channel, which, provided the elliptic curve discrete log problem is intractable, leaks no useful information about $a, b \in \mathbb{F}_p$.

This protocol is often used to exchange a cryptographic key to be used in a symmetric encryption algorithm and is used in protocols such as SSH, HTTPS, and a variant of it in the Signal Protocol.

## What does a Diffie-Hellman Key Exchange look like?

In practice, each of the two parties performs the following.

1. Generate a local secret $a \in \mathbb{F}_p$ with a cryptographically secure pseudorandom number generator.
2. Add the generator point $G \in E(\mathbb{F}_p)$ to itself $a$ times via elliptic curve point addition and doubling.
3. Publish the generated point $A \in E(\mathbb{F}_p)$ so the other party can receive it.
4. Receive the other party's generated point $B \in E(\mathbb{F}_p)$
5. Add the other party's generated point $B$ to itself $a$ times via elliptic curve point addition and doubling.
6. The generated point is the shared secret.

## Tripartite Diffie-Hellman

A variant of the Diffie-Hellman key exchange protocol is the tripartite Diffie-Hellman key exchange. There are a few variants with different tradeoffs, but we focus on single-round tripartite Diffie-Hellman, which enables a single transmission from each party, irrespective of ordering.

However, for the single-round tripartite Diffie-Hellman, we use the bilinearity of an elliptic curve pairing. The elliptic curves over which the pairing exists are $E(\mathbb{F}_p)$ as above and $E(\mathbb{F}_{p^2})$, which is the same elliptic curve function but with scalars as elements of a polynomial field extension $\mathbb{F}_{p^2}$. The ellipitic curve pairing function is $e : E(\mathbb{F}_p) \times E(\mathbb{F}_{p^2}) \rightarrow \mathbb{F}_{p^{12}}$, where the output is an element of a polynomial extension field of degree 12. Alice, Bob, and Charlie agree on two generator points $G_1 \in E(\mathbb{F}_p)$ and $G_2 \in E(\mathbb{F}_{p^2})$, each chose their respective secret scalar $a, b, c \in \mathbb{F}_p$, compute their respective points in both curves $[a]G_1, [b]G_1, [c]G_1 \in E(\mathbb{F}_p)$ and $[a]G_2, [b]G_2, [c]G_2 \in E(\mathbb{F}_{p^2})$, each transmits their respective pairs: $(A_1, A_2), (B_1, B_2), (C_1, C_2)$, then on receiving the other two pairs, compute the elliptic curve pairing and exponentiate the result by their own secret.

Alice:

$$e(B, C)^a = e([b]G_1, [c]G_2)^a = e(G_1, G_2)^{abc}$$

Bob:

$$e(A, C)^b = e([a]G_1, [c]G_2)^b = e(G_1, G_2)^{bac}$$

Charlie:

$$e(A, B)^c = e([a]G_1, [b]G_2)^c = e(G_1, G_2)^{cab}$$

Finally:

$$e(G_1, G_2)^{abc} = e(G_1, G_2)^{bac} = e(G_1, G_2)^{cab}$$

Note that the ordering of points works out the same, that is to say $e(A_1, B_2) = e(B_1, A_2)$.

The steps for each party are as follows.

1. Generate a local secret $a \in \mathbb{F}_p$ with a cryptographically secure pseudorandom number generator.
2. Add the generator point of each curve $G_1 \in E(\mathbb{F}_p)$ and $G_2 \in E(\mathbb{F}_{p^2})$ to itself $a$ times via elliptic curve point addition and doubling.
3. Publish the generated pair $(A_1, A_2) \in (E(\mathbb{F}_p), E(\mathbb{F}_{p^2}))$ so the other parties can receive it.
4. Receive the other parties' pairs of generated points $(B_1, B_2)$ and $(C_1, C_2)$
5. Compute the ellptic curve pairing $e(B_1, C_2)$ (or $e(C_1, B_2)$).
6. Exponentiate the output of the elliptic curve pairing to the power of $a$: $e(B_1, C_2)^a$
7. The final scalar in $\mathbb{F}_{p^{12}}$ is the shared secret.

## References

1. [Pairings for Beginners (PDF)](https://static1.squarespace.com/static/5fdbb09f31d71c1227082339/t/5ff394720493bd28278889c6/1609798774687/PairingsForBeginners.pdf)
