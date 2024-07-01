# ChaCha Encryption

- ChaCha's core is a permutation $P$ that operates on 512-bit strings
- operates on ARX based design: add, rotate, xor. all of these operations are done 32-bit integers
- $P$ is supposed to be secure instantiation of *random permutation* and constructions based on $P$ are analysed in *random-permutation* model.
- using permutation $P$, a pseudorandom function $F$ is constructed that takes a 256 bit key and 128-bit input to 512-bit output with a 128-bit *constant*.

$$
F_{k}(x)\xlongequal{def} P(\operatorname{const} \parallel k \parallel x)\boxplus \operatorname{const} \parallel k \parallel x
$$

Then, chacha stream cipher's internal state is defined using $F$ with a 256-bit seed $s$ and 64-bit initialisation vector $IV$ and 64-bit nonce that is used only once for a seed. Often defined as a 4x4 matrix with each cell containing 4 bytes:

|         |         |        |        |
| ------- | ------- | ------ | ------ |
| "expa"  | "nd 3"  | "2-by" | "te k" |
| Key     | Key     | Key    | Key    |
| Key     | Key     | Key    | Key    |
| Counter | Counter | Nonce  | Nonce  |


Let's define what happens inside $F$, it runs a quarter round that takes as input 4 4-byte input and apply constant time ARX operations:

```
a += b; d ^= a; d <<<= 16;
c += d; b ^= c; b <<<= 12;
a += b; d ^= a; d <<<= 8;
c += d; b ^= c; b <<<= 7;
```

**quarter round** is run 4 times, for each column and 4 times for each diagonal. ChaCha added diagonal rounds from row rounds in Salsa for better implementation in software. Quarter round by itself, is an invertible transformation, to prevent this, ChaCha adds initial state back to the quarter-round outputs.

This completes 1 round of block scrambling and as implied in the name, ChaCha20 does this for 20 similar rounds. [ChaCha family][chacha-family] proposes different variants with different rounds, namely ChaCha8, ChaCha12.

**Nonce** can be increased to 96 bits, by using 3 nonce cells. [XChaCha][xchacha] takes this a step further and allows for 192-bit nonces.

Reason for constants:
- prevents zero block during cipher scrambling
- attacker can only control 25% of the block, when given access to counter as nonce as well.

During initial round, **counters** are initialised to 0, and for next rounds, increase the counter as 64-bit little-endian integer and scramble the block again. Thus, ChaCha can encrypt a maximum of $2^{64}$ 64-byte message. This is so huge, that we'll never ever require to transmit this many amount of data. [IETF][ietf] variant of ChaCha only has one cell of nonce, i.e. 32 bits, and thus, can encrypt a message of $2^{32}$ 64-byte length, i.e. 256 GB.

[uct]: <https://www.cryptography-textbook.com/book/>
[ietf]: <https://datatracker.ietf.org/doc/html/rfc8439>
[xchacha]: <https://www.cryptopp.com/wiki/XChaCha20>
[salsa]: <https://cr.yp.to/snuffle.html>
[chacha]: <https://cr.yp.to/chacha.html>
[chacha-family]: <https://cr.yp.to/chacha/chacha-20080128.pdf>