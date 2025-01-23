# Curves
Everything in `ronkathon` (and much of modern day cryptography) works with elliptic curves $E$ as primitives.
Simply put, an elliptic curve is a curve defined by the equation $y^2 = x^3 + ax + b$ where $a$ and $b$ are constants that define the curve.
When working over a finite field so that $x, y a, b \in \mathbb{F}_q$, we put $E(\mathbb{F}_q)$ to denote the set of points on the curve over the field $\mathbb{F}_q$.
It turns out that the set of points $E(\mathbb{F}_q)$ forms a group under a certain operation called point addition.
This group, in at least certain cases, is discrete logarithm hard, which is the basis for much of modern day cryptography.

## Curve Group and Pluto Curve
For the sake of `ronkathon`, we use a specific curve which we affectionately call the "Pluto Curve."
Our equation is:
$$y^2 = x^3 + 3$$
and we work with the field $F_p$ and $F_{p^2}$ where $p = 101$.
Predominantly, we use the extension $F_{p^2}$ since we need this for the [Tate pairing](https://en.wikipedia.org/wiki/Tate_pairing) operation.
We refer to $F_{101}$ as the `PlutoBaseField` and $F_{101^2}$ as the `PlutoBaseFieldExtension` within `ronkathon`.
From which, we also use the terminology of `PlutoCurve` to refer to $E(F_{101})$ and `PlutoExtendedCurve` to refer to $E(F_{101^2})$.

We also define a `CurveGroup`, an extension of [`FiniteGroup`](../algebra/group/mod.rs) trait representing the group law of the curve.

### Type B curve and type 1 pairing

Investigating our curve and choice of field, we find that the curve is Type B since:

- It is of the form $y^2 = x^3 + b$;
- $p = 101 \equiv 2 \mod 3$;
It follows that $E(\mathbb{F}_{101})$ is [supersingular](https://en.wikipedia.org/wiki/Supersingular_elliptic_curve) which implies that the `PlutoCurve` has order (number of points) $n = 101 + 1 = 102$ and `PlutoExtendedCurve` has order $n^2 = 102^2 = 10404$.
Finally, the embedding degree of the curve is $k=2$.
- This curve has a 17-torsion subgroup calculated as largest prime factor of order of curve `102 = 17.2.3`.

Since, the curve is supersingular, this allows us to define the type-1 Tate pairing $e \colon G_{1} \times G_{2} \to F_{p^2}^{*}$ in a convenient manner, where both $G_{1},G_{2}\in\mathcal{G}_{1}$, i.e. the base field subgroup of r-torsion subgroup.

In particular, we can pick $\mathbb{G}_{1}$ to be the [$r$-torsion subgroup](https://crypto.stanford.edu/pbc/notes/elliptic/torsion.html) of `PlutoCurve` where $r = 17$ is the [scalar field](https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication) of the curve.
Note that $r=17$ is valid since $17 \nmid 101-1$ and $17 \mid 101^2 -1$ ([Balasubramanian-Koblitz theorem](https://crypto.stanford.edu/pbc/notes/ep/bk.html)).

In this case, we pick $G = Z_{17}$ and define our pairing as:
$$e(P, Q) = f(P, \Psi(Q))^{(p^2-1)/r}$$
where $f$ is the Tate pairing and $\Psi$ is the map $\Psi(x,y) = (\zeta x, y)$ where $\zeta$ is a primitive cube root of unity.
This is due to the fact that $\Psi$ is the distortion map that maps a factor of $E(F_{101^2})[17] \cong Z_{17} \times Z_{17}$ (which is the $17$-torsion group) to the other.

## Pairing and Miller's algorithm

Let's dive a little bit deeper into divisors, and miller's algorithm.

Divisors  essentially are just a way to represent [zeroes and poles](https://crypto.stanford.edu/pbc/notes/elliptic/divisor.html) of a [rational function](https://crypto.stanford.edu/pbc/notes/elliptic/map.html). We are interested in divisors of functions evaluated on Elliptic curves, i.e. $\text{div}f=\sum_{P\in E} n_P(P)$.

For example: let's take a function $f=x^3-8$ with $x\in\mathbb{C}$, it's divisor is written as $(f)$ and it has a zero of order 3 at $x=2$ and a pole of order 3 at $x=\infty$, thus, $(f) = 3(2) - 3(\infty)$.

For an elliptic curve, a line usually intersects the curve at 3 points $P,Q,R=(P+Q)$, then the divisor is written as $(l)=(P)+(Q)+(R)-3(O)$. Note all of these divisors are degree-zero divisors as sum of their multiplicities is 0. There's another concept called **support of divisor** = $\text{supp}(D)=\{P\in E:n_P \neq 0\}$.

Now, we have most of the things we need to represent tate pairing:

$$
e(P,Q)=f_P(D_Q)
$$

where $f_P$ is a rational function with $(f_P) = r(P) - r(O)$ and $D_Q$ is the divisor equivalent to $(D_Q)\sim (Q)-(O)$.

### Miller's algorithm

$f_{r,P}$ can be calculated as $f_{r-1,P}\cdot\frac{l_{[r-1]P,P}}{v_{rP}}$ where $l_{[m]P,P}$ is the line from $[m]P$ and $P$, and $v[m]P$ is the vertical line going from $m[P], -[m]P$. Both of these lines are used in chord-and-tangent rule in Elliptic curve group addition law.

Usual naive way is impractical on where $r\sim 2^{160}$, and thus, for practical pairings, Miller's algorithm is used that has $O(\log r)$ time complexity, and uses an algorithm similar to double-and-add algorithm.

## Helpful Definitions
Here are a few related definitions that might be helpful to understand the curve and the pairing.

### roots of unity

the $rth$ root of unity in $F_p$ is some number $h$ such that $h^r \equiv 1$, For example in our field scaler field $F_{101}$ the $4th$ roots of unity are $\{1,10,91,100\}$.

### $r$-torsion

 $r$-torsion points are points $P \in E(K) | rP = O$ for some point $P$ so that $P$  has order $r$  or is a factor of $r$. The set of r-torsion points in $E(K)$ is denoted $E(K)[r]$. If $\bar{K}$ is the [algebraic closure](https://en.wikipedia.org/wiki/Algebraic_closure) of $K$ then the number of r-torsion points in $E(K)$ is the number of points in $E(\bar{K})[r] = r^2$.

- *Security note: If* $r$  and $q$ are not co-prime then the discrete log is solvable in linear time with something called an anomaly attack.

### Frobenius endomorphism

Curve endomorphisms are maps that take points in one a curve subgroup and map them to themselves. An example is point addition and point doubling. The Frobenius endomorphism denoted $\Phi$  takes points in $P \in E(F_q)$ and maps them $\Phi(P) = (X^q, Y^q)$ .

For higher powers of  the map you write $\Phi^k$ .

### Trace Map

This then allows us to define the trace map which takes points in $E(F_{q^k})$ and maps them to $E(F_q)$

$$
tr(P) = P + \Phi(P ) + ... + \Phi^{k−1}(P )
$$

Since $k=2$ in our parameters we get $tr(P) = P + \Phi(P)$.

**Trace Zero Subgroup:** The set of points of trace zero $G = \{P | tr P = O\}$ is a cyclic group of order $r$, and every $P \in G$ satisﬁes $\Phi(P ) = qP$ .

### Quadratic Non Residue

A Quadratic Non-residue is a number that, cannot be expressed as a square of any other number. In other words, for a given modulus $n$, a number $b$ is a quadratic non-residue if there is no number a satisfying the congruence $a^2 ≡ b$  (mod n).

An example of quadratic non-residues would be the number 2 in modulo 3, 4, or 5. In these cases, there is no integer that we can square and then divide by the given modulus to get a remainder of 2.

## References
Note that most of these are gross over-simplification of actual concepts and we advise you to refer to these references for further clarifications.

- [Ben Lynn's Thesis](https://crypto.stanford.edu/pbc/thesis.pdf)
- [Craig Costello's PairingsForBeginners](https://static1.squarespace.com/static/5fdbb09f31d71c1227082339/t/5ff394720493bd28278889c6/1609798774687/PairingsForBeginners.pdf)
- [Pairings in depth](https://static1.squarespace.com/static/5fdbb09f31d71c1227082339/t/5ff394720493bd28278889c6/1609798774687/PairingsForBeginners.pdf)
