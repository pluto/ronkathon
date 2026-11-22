# Primality Testing

Many schemes need large primes: RSA multiplies two of them, Diffie-Hellman and DSA work in groups of prime order, and prime fields are the base of most elliptic curve cryptography. Trial division up to $\sqrt{n}$ is far too slow for numbers of cryptographic size, so primes are found with fast tests instead.

## Fermat test

By Fermat's little theorem, $a^{n-1} \equiv 1 \pmod n$ for a prime $n$ and any $a$ not divisible by $n$. So if $a^{n-1} \not\equiv 1$, then $n$ is composite. The converse doesn't hold: Carmichael numbers like $561 = 3 \cdot 11 \cdot 17$ satisfy $a^{n-1} \equiv 1$ for every $a$ coprime to them, so the Fermat test can't catch them.

## Miller-Rabin

Miller-Rabin strengthens the Fermat test with one more fact: modulo a prime, the only square roots of $1$ are $1$ and $-1$.

Write $n - 1 = d \cdot 2^s$ with $d$ odd. For a base $a$, look at

$$a^d, a^{2d}, a^{4d}, \dots, a^{2^s d} = a^{n-1} \pmod n.$$

Each term is the square of the one before. If $n$ is prime, the last term is $1$, and walking back from it the first term that isn't $1$ has to be $-1$. So either $a^d \equiv 1$, or $a^{2^r d} \equiv -1$ for some $0 \le r < s$. If neither happens, $a$ is a *witness* that $n$ is composite.

For an odd composite $n$, at most a quarter of the bases fail to be witnesses. Testing $k$ random bases wrongly calls a composite prime with probability at most $4^{-k}$, and a prime is never rejected. This is [`miller_rabin`](mod.rs).

For bounded inputs the bases can be fixed instead: testing the first twelve primes $2, 3, \dots, 37$ as bases gives the right answer for every $n < 2^{64}$, which is what [`is_prime`](mod.rs) does.

## Generating primes

[`random_prime`](mod.rs) draws random odd numbers with the top bit set, so they have exactly the requested number of bits, and returns the first one that passes. By the prime number theorem about $1$ in $\ln(2^{b}) / 2$ odd $b$-bit numbers is prime, roughly $1$ in $22$ for $64$ bits, so only a few candidates are needed.
