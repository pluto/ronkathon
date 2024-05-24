# Curves
Everything in `ronkathon` (and much of modern day cryptography) works with elliptic curves $E$ as primitives.
Simply put, an elliptic curve is a curve defined by the equation $y^2 = x^3 + ax + b$ where $a$ and $b$ are constants that define the curve.
When working over a finite field so that $x, y a, b \in \mathbb{F}_q$, we put $E(\mathbb{F}_q)$ to denote the set of points on the curve over the field $\mathbb{F}_q$.
It turns out that the set of points $E(\mathbb{F}_q)$ forms a group under a certain operation called point addition.
This group, in at least certain cases, is discrete logarithm hard, which is the basis for much of modern day cryptography.

## Pluto Curve
For the sake of `ronkathon`, we use a specific curve which we affectionately call the "Pluto Curve."
Our equation is:
$$y^2 = x^3 + 3$$
and we work with the field $\mathbb{F}_{p}$ and $\mathbb{F}_{p^2}$ where $p = 101$.
Predominantly, we use the extension $\mathbb{F}_{p^2}$ since we need this for the [Tate pairing](https://en.wikipedia.org/wiki/Tate_pairing) operation.
We refer to $\mathbb{F}_{101}$ as the `PlutoBaseField` and $\mathbb{F}_{101^2}$ as the `PlutoBaseFieldExtension` within `ronkathon`.
From which, we also use the terminology of `PlutoCurve` to refer to $E(\mathbb{F}_{101})$ and `PlutoExtendedCurve` to refer to $E(\mathbb{F}_{101^2})$.

### Type B curve and type 1 pairing

Investigating our curve and choice of field, we find that the curve is Type B since:

- It is of the form $y^2 = x^3 + b$;
- $p = 101 \equiv 2 \mod 3$;
It follows that $E(\mathbb{F}_{101})$ is [supersingular](https://en.wikipedia.org/wiki/Supersingular_elliptic_curve) which implies that the `PlutoCurve` has order (number of points) $n = 101 + 1 = 102$ and `PlutoExtendedCurve` has order $n^2 = 102^2 = 10404$.
Finally, the embedding degree of the curve is $k=2$.

Since, the curve is supersingular, this allows us to define the type-1 Tate pairing $e \colon \mathbb{G}_{1} \times \mathbb{G}_{2} \to \mathbb{F}_{p^2}^{*}$ in a convenient manner, where both $\mathbb{G}_{1},\mathbb{G}_{2}\in\mathcal{G}_{1}$, i.e. the base field subgroup of r-torsion subgroup.

In particular, we can pick $\mathbb{G}_{1}$ to be the [$r$-torsion subgroup](https://crypto.stanford.edu/pbc/notes/elliptic/torsion.html) of `PlutoCurve` where $r = 17$ is the [scalar field](https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication) of the curve.
Note that $r=17$ is valid since $17 \nmid 101-1$ and $17 \mid 101^2 -1$ ([Balasubramanian-Koblitz theorem](https://crypto.stanford.edu/pbc/notes/ep/bk.html)).

In this case, we pick $G = \mathbb{Z}_{17}$ and define our pairing as:
$$e(P, Q) = f(P, \Psi(Q))^{(p^2-1)/r}$$
where $f$ is the Tate pairing and $\Psi$ is the map $\Psi(x,y) = (\zeta x, y)$ where $\zeta$ is a primitive cube root of unity.
This is due to the fact that $\Psi$ is the distortion map that maps a factor of $E(\mathbb{F}_{101^2})[17] \cong \mathbb{Z}_{17} \times \mathbb{Z}_{17}$ (which is the $17$-torsion group) to the other.