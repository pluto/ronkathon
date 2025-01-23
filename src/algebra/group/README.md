# Group

## Traits
- `Group`: a generic group $(G, \cdot)$ where $G$ is a set and $\cdot$ is a binary operation.
- `FiniteGroup`: a group with finite elements defined using `Finite` trait
- `AbelianGroup`: group with commutative operation
- `FiniteCyclicGroup`: a finite group with a generator.

### `Group`
[`Group`](./mod.rs) represents a group with finite elements. It defines a binary operation on the set of elements of the group.
- `IDENTITY`: The identity element of the group.
- `inverse(&self) -> Self`: inverse of the element.
- `operation(a: &Self, b: &Self) -> Self`: the operation of the group.
- `scalar_mul(&self, scalar: &Self::Scalar)`: multiplication of the element by a scalar.

## Structs
The structs that implement these traits are
- `MultiplicativePrimeGroup`

### `MultiplicativePrimeGroup`
The `MultiplicativePrimeGroup` struct is a wrapper around a `usize` that defines $(Z/nZ)^{*}$ for a prime power $n=p^k$ with binary operation as $\times$:
```rust
pub struct MultiplicativePrimeGroup<const P: usize, const K: usize>(usize);
```

It uses compile time assertions to check that $P$ is prime.

## Examples

[Symmetric Group](../../../examples/symmetric_group.rs) example showcases how `Group` trait is implemented for any struct.
