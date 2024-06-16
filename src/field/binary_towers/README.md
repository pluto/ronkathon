## Binary Fields

[Binary fields](https://en.wikipedia.org/wiki/GF%282%29) denoted as $GF(2)=Z/2Z$, i.e. quotient ring of integers modulo ring of 2 integers $\{0,1\}, are a special class of Finite Fields, with modulus = $2$. Main properties exhibited by Binary fields are:
- Addition corresponds to bitwise XOR
- Multiplication corresponds to bitwise AND
- since, $x+x=0\implies x=-x$, i.e. negation of a number is itself

This allows for extremely efficient arithmetic that is much more hardware friendly than fields based on other primes.

## Binary Extension fields

Finite field with $2^{k}$ elements represented as $GF(2^k)=F(2)[X]/f(X)$, where $f(X)$ is an irreducible of degree $k$. Used extensively in cryptography like AES block cipher and error-correcting codes.

Two ways of representing $GF(2^{k})$:

- univariate basis - two ways of representing in univariate basis as well, namely:
    - polynomial basis: elements are represented as degree k-1 polynomial $A_{k-1}\alpha^{k-1}+\dots+A_1\alpha+A_0$ by equivalence class $GF(2)/f(x)$, where f(x) is any irreducible in the kth power.
    - normal basis: elements are represented as taking powers of an element from the field
- multilinear basis: there’s one other way of representing elements, i.e. Multilinear basis, where elements are represented by monomials: $1,X_0,X_1\cdot X_0,X_2\cdot X_1\cdot X_0,\dots,X_0\dots X_{l-1}$, with each coefficient in $GF(2)$.

### Extension field using towers 

[Binius](https://eprint.iacr.org/2023/1784.pdf) realises binary extension field using towers formalised in [Weidemann et al.](https://www.fq.math.ca/Scanned/26-4/wiedemann.pdf).

Basic idea is to derive sequence of polynomial rings inductively

- start with $\tau_{0}=\mathbb{F}_{2}=\{ 0,1 \}$
- set $\tau_{1}=\tau_{0}[X_{0}]/(X_{0}^{2}+X_{0}+1)=\mathbb{F}_{2^{2}}$, namely $\{ 0,1,X_{0},1+X_{0} \}$.
- set $\tau_{2}=\tau_{1}[X_{1}]/(X_{1}^{2}+X_{0}X_{1}+1)=\mathbb{F}_{2^{2^{2}}}$
- continue this further with $\tau_{0}\subset \tau_{1}\subset\dots \subset \tau_{i-1}\subset \tau_{i}=\tau_{i-1}[X_{i-1}]/f_{i-1}(X_{i-1})$, where $f_{i-1}(X_{i-1})=X_{i-1}^{2}+X_{i-1}X_{i-2}+1$ is an irreducible in $\tau_{i}$
