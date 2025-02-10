# Hash Functions 

A hash function is a function that take in an input of arbitrary length, and produces a fixed length output.
Moreover, a hash function should be deterministic, meaning that the same input should always produce the same output.
Also, we require that the output of a hash function should be uniformly distributed over its output space, meaning that every output should be equally likely given any input.

Intuitively, you can imagine the job for a hash function is to take some arbitrary data and produce a unique "identifier" or "fingerprint" for that data.
Given that the output space is large enough (and some other conditions are met), we can use hash functions to do this. 
In effect, every bit of data we care to create an identifier for can be hashed to a unique output value.
For instance, we may have a complete library of works of literature, and by hashing the contents of each book, we can create a unique identifier for each book.
Common output spaces are 256-bits, meaning that we would have 2^256 possible outputs.
To put this in perspective, the number of atoms in the observable universe is estimated to be around 10^80, which is around the magnitude of 2^256.
For back of the envelope calculations, we can note that 2^10 is about 1000=10^3, so 2^256 is about 10^77, which is near the estimates of number of atoms in the observable universe.

## SHA-2
[SHA-2](https://en.wikipedia.org/wiki/SHA-2) is a family of hash functions that includes SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224, and SHA-512/256.
The SHA-2 family of hash functions are widely used and are considered to be secure, though you should not hash secrets directly with SHA-2 (you can use SHA-3 instead).
As with many cryptographic primitives, SHA-2 is standardized by NIST.
It is used in many different protocols such as TLS, SSL, PGP, and SSH.

The hash function itself is based on the [Merkle-Damgard construction](https://en.wikipedia.org/wiki/Merkle–Damgård_construction), so it reads in blocks of data and processes them in a certain way.
The output of the hash function is the hash of the data, which is a fixed length output.
In our case, we will be using SHA-256, which produces a 256-bit output.

For more detail on the implementation of SHA-256 see [this resource](https://helix.stormhub.org/papers/SHA-256.pdf).
Also, you can find JavaScript code and a working applet for SHA-256 [here](https://www.movable-type.co.uk/scripts/sha256.html).
Our implementation can be found in the `src/hashes/sha256.rs` file with detailed documentation and comments.

## SHA-3
 Unlike SHA-2, which was built using the Merkle-Damgård construction, SHA-3 is based on the Keccak sponge construction.

### Why SHA-3 over SHA-2?
1. **Different Architecture**: SHA-3 uses the sponge construction which is fundamentally different from SHA-2's Merkle-Damgård construction. This diversity is valuable - if a weakness is found in one construction, we have a backup.

2. **Security**: While SHA-2 remains secure, SHA-3 offers:
   - Better resistance against length extension attacks
   - Simpler design making cryptanalysis easier
   - Higher performance in hardware implementations
   - More flexibility through its sponge construction

3. **Handling Secrets**: SHA-3 is more suitable for hashing secret values because it's naturally resistant to length extension attacks, unlike SHA-2 which requires additional constructions (like HMAC) for secure secret handling.

### The Sponge Construction
SHA-3 uses the sponge construction which works in two phases:
1. **Absorbing Phase**: Input data is "absorbed" into the sponge state
2. **Squeezing Phase**: Output is "squeezed" from the state

This construction allows for:
- Variable length input
- Variable length output
- Simple parallel implementation
- Natural resistance to length extension attacks

## Extendable Output Functions (XOF)
XOFs are a special type of hash function that can produce outputs of any desired length. SHA-3 includes two standardized XOF variants:
- SHAKE128
- SHAKE256

### Why Use XOFs?
1. **Flexibility**: Unlike traditional hash functions with fixed output sizes, XOFs can produce arbitrary-length outputs.

2. **Efficiency**: When you need multiple different-length hashes of the same input, an XOF is more efficient than running multiple hash functions.

3. **Key Derivation**: XOFs are particularly useful for key derivation functions where you might need different length keys from the same input.

### Security Considerations
- SHAKE128 provides 128-bit security strength
- SHAKE256 provides 256-bit security strength
- The security strength remains constant regardless of output length
- Longer output lengths do not increase security, they just provide more output bits

### Use Cases
1. **Key Derivation**: Generating multiple keys of different lengths
2. **Random Number Generation**: Creating arbitrary-length pseudorandom bits
3. **Hash-based Signatures**: Schemes requiring variable-length hashes
