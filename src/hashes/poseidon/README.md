Contains implementation of [Poseidon](https://eprint.iacr.org/2019/458.pdf) hash function by Grassi et al..
It's main feature is that it's an algebraic hash function suitable for usage in arithmetic proof
systems like SNARKs, and modularity with respect to choosing different parameters according
to the use case.

Uses mix of following computations at each step:
- round constants: predetermined constants added to each element in state.
- non-linear layer: in the form of s-box
- linear layer: use an MDS (maximally distance separable) matrix of dimensions `width * width`
  and perform matrix multiplication with state.

Uses the [Hades](https://eprint.iacr.org/2019/1107) permutation design strategy and thus, it's round function can be divided into two kinds:
- Partial rounds: non-linear layer is only applied to first element of the state
- Full rounds: non-linear layer is applied to all elements

Security of the function depends mainly on:
- Number of full rounds
- Number of partial rounds
- at each round, the exponent in s-box, choice of matrix in linear layer

rounds are applied in a chaining fashion:
- first, half of full rounds are performed
- then, all partial rounds
- then, half of remaining full rounds
- first element in state is returned as hash output

## Permutation

Hash function permutation is responsible for blending the elements to remove any symmetrical properties in the input using round functions.

Permutation at each round of Poseidon works as follows:
- For full rounds $R_f$:
  - round constants are added to each element in state
  - s-box is applied, i.e. each element is raised to power of **`alpha`**
  - elements are mixed using linear layer by matrix multiplication with MDS matrix
- For partial rounds $R_p$:
  - round constants are applied same as full rounds
  - s-box is applied only to first element
  - linear layer is applied

Rounds constants add external information to the state and break any symmetrical and structural properties in the input. Poseidon uses Grain LFSR to generate round constants.

S-Boxes imparts non-linearity in the input data. Non-linearity prevents linear attacks which aim to exploit linear relation between round operations. Poseidon uses power of elements, generally $x^3, x^5$, calculated as minimum value such that $\gcd(\alpha, p-1) = 1$.

MDS (Maximally distance separable) matrix are uses in the linear layer of the round. Its main use is to mix the elements together such that any changes made in the non-linear layer are spread throughout the state. Maximally distance separable refers to matrices such that no two rows are linear dependent to each other. This maximises the input differences across the hash state.

## Sponge API

[Sponge](https://en.wikipedia.org/wiki/Sponge_function) allow to take as input, data of arbitrary size and produce variable length output.

Each hash functions' state is divided into two sections:
- `rate`: rate at which new elements are absorbed by the sponge
- `capacity`: remaining elements in sponge state.

Sponge behavior, based on `Sponge` metaphor which can be explained by following functions:
- `Absorb`: absorbs new field elements $\mathbb{F}_p$ into sponge state.
  - For example: if sponge width is `10` units and sponge rate is `3`, then if a `15` unit input is entered, its divided into `5` chunks of `3` units and added to sponge state.
  - After each chunk addition, permutation is performed, until all chunks are absorbed.
- `Squeeze`: after the absorption, hash's output is returned using squeezing of sponge state.
  - For example: for a sponge with width of `10` units and rate of `3`, if hash output of `25` units is required, then:
  - `width` number of elements are squeezed out of sponge state at each iteration.
  - permutation is performed until required number of elements are squeezed out.

> [!NOTE]
> Only `rate` section is acted upon in `absorb` and `squeeze` of Sponge API, and `capacity` section is left untouched. Absorption of new elements and squeeze output is taken from `rate` section. This allows permutation to mix the elements thoroughly.

Absorption operation can be different for different hash functions. For example: Keccak uses xor to absorb new elements. Since Poseidon is an algebraic hash function and based on finite fields, it uses addition of field elements.

## Example

First, we need to generate round constants which will be used in poseidon parameters. Poseidon requires following parameters for initialisation:

- $\mathbb{F}_p$: finite field
- `WIDTH`: width of the state of the hash
- `ALPHA`: used in s-box layer
- `NUM_P`: number of partial rounds
- `NUM_F`: number of full rounds
- `rc`: round constants used in round constant layer of a round
- `mds`: matrix used in linear layer of a round

This can be generated using [sage file](../../../math/poseidon_constants.sage) provided at project's core. Run following command to generate a constants file:

- `Usage: <script> <field> <s_box> <field_size> <num_cells> <alpha> <security_level> <modulus_hex>`
- field = 1 for GF(p), 0 for GF(p^k)
- s_box = 0 for x^alpha, s_box = 1 for x^(-1)

```sh
sage poseidon_constants.sage 1 0 7 16 3 10 0x65
```

Here's an example to use [Poseidon](./mod.rs) struct for hashing input of length `WIDTH`. Note that input is padded with extra zeroes if length is not equal to width.

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

// create any input
let input = std::iter::repeat(PlutoBaseField::ZERO).take(WIDTH).collect();

// perform hash operation
let res = poseidon.hash(input);

println!("{:?}", res);
```

Another example using Sponge API for arbitrary length element hashing. Simplex sponge supports arbitrary length absorption with arbitrary length squeeze.

```rust
use rand::rng;
use ronathon::field::prime::PlutoBaseField;

let size = rng.gen::<u32>();

// create any state
let input = std::iter::repeat(PlutoBaseField::ONE).take(size).collect();

let (rc, mds) = load_constants::<PlutoBaseField>();

let mut pluto_poseidon_sponge = PoseidonSponge::new(WIDTH, ALPHA, NUM_P, NUM_F, rate, rc, mds)

let absorb_res = pluto_poseidon_sponge.absorb(&input);
assert!(absorb_res.is_ok());

let pluto_result = pluto_poseidon_sponge.squeeze(squeeze_size);
assert!(pluto_result.is_ok());
```
More info and examples can be found in [tests](./tests/mod.rs).

## Next steps

- [ ] Grain LFSR for round constants generation
- [ ] Duplex sponge
- [ ] Possible attacks using tests

## References

- [Poseidon by Grassi et al.](https://eprint.iacr.org/2019/458)
- [Poseidon Journal](https://autoparallel.github.io/overview/index.html)
- [Sponge API](https://keccak.team/sponge_duplex.html)
