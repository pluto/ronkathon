# Group

## Traits
- `Group`: a generic group $(G, \oplus)$ where $G$ is a set and $\oplus$ is a binary operation.
- `FiniteGroup`: a group with finite elements.
- `FiniteCyclicGroup`: a finite group with a generator.

### `Group`
[`Group`](./group.rs) represents a group with finite elements. It defines a binary operation on the set of elements of the group.
- `IDENTITY`: The identity element of the group.
- `inverse(&self) -> Self`: inverse of the element.
- `operation(a: &Self, b: &Self) -> Self`: the operation of the group.
- `scalar_mul(&self, scalar: &Self::Scalar)`: multiplication of the element by a scalar.

### `FiniteGroup`
- `ORDER`: The order of the group.

### `FiniteCyclicGroup`
- `GENERATOR`: The generator of the group.

## Structs
The structs that implement these traits are
- `MultiplicativePrimeGroup`

### `MultiplicativePrimeGroup`
The `MultiplicativePrimeGroup` struct is a wrapper around a `usize` with binary operation as $\times$:
```rust
pub struct MultiplicativePrimeGroup<const P: usize>(usize);
```
