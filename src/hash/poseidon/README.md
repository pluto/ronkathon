Contains implementation of [Poseidon](https://eprint.iacr.org/2019/458.pdf) hash function by Grassi et al..
It's main feature is that it's an algebraic hash function suitable for usage in arithmetic proof
systems like SNARKs, and modularity with respect to choosing different parameters according
to the use case.

Uses mix of following computations at each step:
- round constants: predetermined constants added to each element in state.
- non-linear layer: in the form of s-box
- linear layer: use an MDS (maximally distance separable) matrix of dimensions `width * width`
  and perform matrix multiplication with state.

Uses the Hades design strategy and thus, it's round function can be divided into two kinds:
- Partial rounds: non-linear layer is only applied to first element of the state
- Full rounds: non-linear layer is applied to all elements

Security of the function depends mainly on:
- Number of full rounds
- Number of partial rounds
- at each round, the exponent in s-box, choice of matrix in linear layer

Permutation at each round of Poseidon works as follows:
- For full rounds:
  - round constants are added to each element in state
  - s-box is applied, i.e. each element is raised to power of `alpha`
  - elements are mixed using linear layer by matrix multiplication with MDS matrix
- For partial rounds:
  - round constants are applied same as full rounds
  - s-box is applied only to first element
  - linear layer is applied

rounds are applied in a chaining fashion:
- first, half of full rounds are performed
- then, all partial rounds
- then, half of remaining full rounds
- first element in state is returned as hash output

## Example

```rust
use ronkathon::field::prime::PlutoBaseField; // can be any field that implements FiniteField trait

const WIDTH: usize = 10;
const ALPHA: usize = 5;
const NUM_P: usize = 16;
const NUM_F: usize = 8;

// load round constants and mds matrix
let (rc, mds) = load_constants::<PlutoBaseField>();

// create a poseidon hash object with empty state
let mut poseidon = Poseidon::<PlutoBaseField>::new(WIDTH, ALPHA, NUM_P, NUM_F, rc, mds);

// create any state
let state = std::iter::repeat(PlutoBaseField::ZERO).take(WIDTH).collect();

// perform hash operation
let res = poseidon.hash(state);

println!("{:?}", res);
```