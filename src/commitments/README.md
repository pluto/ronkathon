# Commitment Schemes

A commitment scheme is the digital version of a sealed envelope. A committer puts a message in the envelope and hands it over (*commit*). Later they open the envelope (*reveal*), and anyone can check that the message inside is the one that was sealed.

A good scheme has two properties:
- **Hiding**: the commitment says nothing about the message until it is revealed.
- **Binding**: once committed, the committer can't open the commitment to a different message.

Commitments show up everywhere in cryptographic protocols: coin flipping over the phone, sealed-bid auctions, and as the building block of zero-knowledge proofs, where a prover commits to its witness or to polynomials before it learns the verifier's challenge.

## The `CommitmentScheme` trait

Every scheme here implements [`CommitmentScheme`](mod.rs):
- `commit(message, rng)` returns the commitment to publish and an opening (the randomness) to keep secret.
- `verify(commitment, message, opening)` checks a revealed message and opening against the commitment.

## Hash commitment

To commit to bytes $m$, pick random bytes $r$ and publish $c = H(r \| m)$, where $H$ is SHA-256 here. To open, reveal $m$ and $r$.

Binding follows from the hash being collision resistant. Hiding needs $r$: without it, anyone could hash each likely message and compare, which is easy when there are only a few possibilities, like "heads" and "tails".

## Pedersen commitment

Let $G$ and $H$ be two generators of a group of prime order $q$, such that nobody knows $h$ with $H = h \cdot G$. To commit to a scalar $m$, pick a random scalar $r$ and publish

$$C = m \cdot G + r \cdot H.$$

- **Hiding** holds even against unbounded adversaries: $r \cdot H$ is a uniformly random group element, so $C$ is too, whatever $m$ is.
- **Binding** relies on the discrete log problem. Someone who knows $h$ can write $C = (m + r h) \cdot G$ and open it to any $m'$ with $r' = r + (m - m') / h$.
- Pedersen commitments are **additively homomorphic**: $C_1 + C_2$ is a commitment to $m_1 + m_2$ with opening $r_1 + r_2$. This is used, for example, to prove relations between committed values without opening them.

The implementation works over any curve in this crate. On the Pluto curves the subgroup only has 17 elements, so the discrete log is trivial and the example is for learning only.
