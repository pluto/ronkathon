# Groups & Fields

[Groups](https://en.wikipedia.org/wiki/Group_(mathematics)) $G$ are algebraic structures which are set and has a binary operation $\oplus$ that combines two elements $a, b$ of the set to produce a third element $a\oplus b$ in the set.
The operation is said to have following properties:
1. Closure: $a\oplus b=c\in G$
2. Associative: $(a\oplus b)\oplus c = a\oplus(b\oplus c)$
3. Existence of Identity element: $a\oplus 0 = 0\oplus a = a$
4. Existence of inverse element for every element of the set: $a\oplus b=0$
5. Commutativity: Groups which satisfy an additional property: *commutativity* on the set of
   elements are known as **Abelian groups**.

[Finite fields](https://en.wikipedia.org/wiki/Finite_field) are instrumental in cryptographic systems.
They are used in elliptic curve cryptography, RSA, and many other cryptographic systems.
This module provides a generic implementation of finite fields via two traits and two structs.
It is designed to be easy to use and understand, and to be flexible enough to extend yourself.

## Traits
- `FiniteGroup`: a [`group`](./mod.rs) $(G, \oplus)$ where $G$ is a set and $\oplus$ is a binary operation.
- `FiniteField`: a field $(\mathbb{F}_p, +,\cdot)$ where $p$ is a prime number.
- `ExtensionField`: an extension of a field $(\mathbb{F}_{p^k}, +,\cdot)$ where $p$ is a prime number and $\mathbb{F}_{p^k}$ is an extension of $\mathbb{F}_p$.

The two traits used in this module are `FiniteField` and `ExtensionField` which are located in the `field` and `field::extension` modules respectively.
These traits are interfacial components that provide the necessary functionality for field-like objects to adhere to to be used in cryptographic systems.

### `FiniteGroup`
[`FiniteGroup`](./group.rs) represents a group with finite elements. It defines a binary operation on the set of elements of the group.
- `ORDER`: The order of the group.
- `IDENTITY`: The identity element of the group.
- `GENERATOR`: The generator of the group.
- `inverse(&self) -> Self`: inverse of the element.
- `operation(a: &Self, b: &Self) -> Self`: the operation of the group.
- `scalar_mul(&self, scalar: &Self::Scalar)`: multiplication of the element by a scalar.

### `FiniteField`
The `FiniteField` trait is used to define a finite field in general.
The trait itself mostly requires functionality from traits in the Rust [`core::ops`](https://doc.rust-lang.org/core/ops/) module such as `Add`, `Sub`, `Mul`, and `Div` (and their corresponding assignment, iterator, and related operations).
In effect, these constraints provide us the algebraic structure of a field.

A bit more specifically, the `FiniteField` trait requires the following associated constants and (const) methods:
- `const ORDER: Self` - The order of the field.
- `const ZERO: Self` - The additive identity.
- `const ONE: Self` - The multiplicative identity.
- `const PRIMITIVE_ELEMENT: Self` - A [primitive element](https://en.wikipedia.org/wiki/Primitive_element_(finite_field)) of the field, that is, a generator of the multiplicative subgroup of the field.
- `inverse(&self) -> Option<Self>` - The multiplicative inverse of a nonzero field element.
Returns `None` if the element is zero.
- `pow(&self, power: usize) -> Self` - Multiply a field element by itself `power` times.
- `primitive_root_of_unity(n: usize) -> Self` - The primitive $n$th root of unity of the field.

### `ExtensionField`
The `ExtensionField` trait is used to define an extension field of a finite field.
It inherits from the `FiniteField` trait and enforces that algebraic operations from the base field are implemented.
It is generic over the prime `P` of the underlying base field as well as the degree `N` of the extension intended.
The only additional constraint aside from the `FiniteField` trait and adherance to algebraic operations on the base field is:
- `const IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS: [PrimeField<P>; N + 1]` - The coefficients of the irreducible polynomial that defines the extension field.

We will discuss `PrimeField<P>` momentarily.

### Constant (Compile Time) Implementations
Note that all of these traits are tagged with `#[const_trait]` which implies that each method and associated constant is implemented at compile time.
This is done purposefully as it allows for generic implementations of these fields to be constructed when you compile `ronkathon` rather than computed at runtime.
In principle, this means the code runs faster, but will compile slower, but the tradeoff is that the cryptographic system is faster and extensible.

We will see examples of this usage next.

## Structs
The structs that implement these traits are
- `MultiplicativePrimeGroup`
- `PrimeField`
- `GaloisField`

> [!NOTE]
> In principal, `PrimeField` and `GaloisField` could be combined into just `GaloisField` but are separated for clarity at the moment.
> These structs are both generic over the prime `P` of the field, but `GaloisField` is also generic over the degree `N` of the extension field.

### `MultiplicativePrimeGroup`
The `MultiplicativePrimeGroup` struct is a wrapper around a `usize` with binary operation as $\times$:
```rust
pub struct MultiplicativePrimeGroup<const P: usize>(usize);
```

### `PrimeField`
The `PrimeField` struct is a wrapper around a `usize` by:
```rust
pub struct PrimeField<const P: usize> {
    value: usize,
}
```
that implements the `FiniteField` trait and has some compile-time constructions.
For example, upon creation of an element of `PrimeField<P>` we utilize the `const fn is_prime<const P: usize>()` function which will `panic!` if `P` is not prime.
**Hence, it is impossible to compile a program for which you construct `PrimeField<P>` where `P` is not prime.**

Furthermore, it is possible to determine the `PRIMITIVE_ELEMENT` of the field at compile time so that we may implement `FiniteField` for any prime `P` without any runtime overhead.
The means to do so is done in the `field::prime::find_primitive_element` function which is a brute force search for a primitive element of the field that occurs as Rust compiles `ronkathon`.

All of the relevant arithmetic operations for `PrimeField<P>` are implemented in `field::prime::arithmetic`.

### `GaloisField`
The `GaloisField` struct is a wrapper around a `PrimeField<P>` by:
```rust
pub struct GaloisField<const N: usize, const P: usize> {
    value: [PrimeField<P>; N],
}
```
where the `[PrimeField<P>; N]` is the representation of the field element as coefficients to a polynomial in the base field modulo the irreducible polynomial of the extension field (recall the `ExtensionField` trait above specifies the need for an irreducible polynomial).

We implement `ExtensionField` for specific instances of `GaloisField<N, P>` as, at the moment, we do not have a general compile-time-based implementation of extension fields as we do with `PrimeField<P>`, though it is possible to do so.
Instead, we have implemented much of the arithmetic operations for `GaloisField<N, P>` in `field::extension::arithmetic`, but left some that needs to be computed by hand for the user to implement (for now).
See, for instance, `field::extension::gf_101_2` implements the `IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS` for `GaloisField<2, 101>` as well as the remaining arithmetic operations.
There is a method to compute both the `IRREDUCIBLE_POLYNOMIAL_COEFFICIENTS` at compile time as well as the `PRIMITIVE_ELEMENT` of the field, but it is not implemented at the moment.