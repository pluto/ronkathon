# AES encryption

[Advanced Encryption Standard][aes] (AES) is a symmetric-key algorithm and is a variant of the Rijndael (pronounced 'rain-dull') block cipher. AES supersedes the [Data Encryption Standard][des] (DES).

## Overview

AES supports a block size of 128 bits, and three different key lengths: 128, 192, and 256 bits. It manipulates _bytes_ instead of _individual bits_ or _64-bit words_, and views a 16-byte plaintext as a 2D column-major grid of bytes.

AES uses [Substitution-Permutation Network (SPN)][spn] which makes use of two main properties: _confusion_ and _diffusion_. Confusion means that the input undergoes complex transformations, and diffusion means that these transformations depend equally on all bits of the input.

Unlike DES, it does not use a Feistel network, and most AES calculations are done in a particular finite field.


## Algorithm 

The core encryption algorithm consists of the following routines:

- [KeyExpansion][keyexp]
- [AddRoundKey][arc]
- [SubBytes](#SubBytes)
- [ShiftRows](#ShiftRows)
- [MixColumns](#MixColumns)

For decryption, we take the inverses of these following routines:

- [InvSubBytes](#InvSubBytes)
- [InvShiftRows](#InvShiftRows)
- [InvMixColumns](#InvMixColumns)

Note that we do not need the inverses of [KeyExpansion][keyexp] or [AddRoundKey][arc], since for decryption we're simply using the round keys from the last to the first, and [AddRoundKey][arc] is its own inverse.

### Encryption

Encryption consists of rounds of the above routines, with the number of rounds being determined by the size of the key. Keys of length 128/192/256 bits require 10/12/14 rounds respectively.

Round *1* is always just *AddRoundKey*. For rounds *2* to *N-1*, the algorithm uses a mix of *SubBytes*, *ShiftRows*, *MixColumns*, and *AddRoundKey*, and the last round is the same except without *MixColumns*.

#### KeyExpansion 

The **KeyExpansion** algorithm takes a 128/192/156-bit key and turns it into 11/13/15 round keys respectively of 16 bytes each. The main trick to key expansion is the fact that if 1 bit of the encryption key is changed, it should affect the round keys for several rounds.

Using different keys for each round protects against _[slide attacks]_.

To generate more round keys out of the original key, we do a series of word rotation and/or substitution XOR'd with round constants, depending on the round number that we are in.

For round **i**, if i is a multiple of the length of the key (in words):

```rust
    Self::rotate_word(&mut last);
    word = (u32::from_le_bytes(Self::sub_word(last))
      ^ u32::from_le_bytes(ROUND_CONSTANTS[(i / key_len) - 1]))
    .to_le_bytes();
```

if i + 4 is a multiple of 8:

```rust
    word = Self::sub_word(last)
```

The final step is always to XOR previous round's round key with the *(i - key_len)*-th round key:

```rust
      let round_key = expanded_key[i - key_len]
        .iter()
        .zip(last.iter())
        .map(|(w, l)| w ^ l)
        .collect_vec()
        .try_into()
        .unwrap();
```

#### AddRoundKey

XORs a round key to the internal state.

#### SubBytes

Substitutes each byte in the `State` with another byte according to a [substitution box](#substitution-box).

#### ShiftRow

Do a **left** shift i-th row of i positions, for i ranging from 0 to 3, eg. Row 0: no shift occurs, row 1: a left shift of 1 position occurs.

#### MixColumns

Each column of bytes is treated as a 4-term polynomial, multiplied modulo x^4 + 1 with a fixed polynomial
a(x) = 3x^3 + x^2 + x + 2. This is done using matrix multiplication.

More details can be found [here][mixcolumns].


### Decryption

For decryption, we use the inverses of some of the above routines to decrypt a ciphertext. To reiterate, we do not need the inverses of [KeyExpansion][keyexp] or [AddRoundKey][arc], since for decryption we're simply using the round keys from the last to the first, and [AddRoundKey][arc] is its own inverse.


#### InvSubBytes

Substitutes each byte in the `State` with another byte according to a [substitution box](#substitution-box). Note that the only difference here is that the substitution box used in decryption is derived differently from the version used in encryption.

#### InvShiftRows

Do a **right** shift i-th row of i positions, for i ranging from 0 to 3, eg. Row 0: no shift occurs, row 1: a right shift of 1 position occurs.

#### InvMixColumns

Each column of bytes is treated as a 4-term polynomial, multiplied modulo x^4 + 1 with the inverse of the fixed polynomial
a(x) = 3x^3 + x^2 + x + 2 found in the [MixColumns] step. The inverse of a(x) is a^-1(x) = 11x^3 + 13x^2 + 9x + 14. This multiplication is done using matrix multiplication.

More details can be found [here][mixcolumns].


## Substitution Box

A substitution box is a basic component of symmetric key algorithms
performs substitution. It is used to obscure the relationship
the key and the ciphertext as part of the *confusion* property.

During substitution, a byte is interpreted as a polynomial and
mapped to its multiplicative inverse in [Rijndael's finite field][Rijndael ff]: GF(2^8) = GF(2)[x]/(x^8 + x^4 + x^3 + x + 1).

The inverse is then transformed using an affine transformation which is the sum of multiple rotations of the byte as a vector, where addition is the XOR operation. The result is an 8-bit output array which is used to substitute the original byte.

## Security

Fundamentally, AES is secure because all output bits depend on all input bits in some complex, pseudorandom way. The biggest threat to block ciphers is in their modes of operation, not their core algorithms.

## Practical implementations

In production-level AES code, fast AES software uses special techniques called table-based implementations which replaces the *SubBytes-ShiftRows-MixColumns* sequence with a combination of XORs and lookups in hardcoded tables loaded in memory during execution time.

## References 

- [FIPS197](fips197)
- [Serious Cryptography - A Practical Introduction to Modern Cryptography](seriouscrypto)

[aes]: https://en.wikipedia.org/wiki/Advanced_Encryption_Standard
[des]: ../des/README.md
[spn]: https://en.wikipedia.org/wiki/Substitution%E2%80%93permutation_network
[slide attacks]: https://en.wikipedia.org/wiki/Slide_attack
[keyexp]: #KeyExpansion
[arc]: #AddRoundKey
[mixcolumns]: https://en.wikipedia.org/wiki/Rijndael_MixColumns
[Rijndael ff]: https://en.wikipedia.org/wiki/Finite_field_arithmetic#Rijndael's_(AES)_finite_field
[fips197]: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf
[seriouscrypto]:https://nostarch.com/seriouscrypto
