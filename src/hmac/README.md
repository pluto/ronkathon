# HMAC (Hash-based Message Authentication Code)

## Overview

HMAC is a cryptographic primitive for providing message integrity and authenticity using a cryptographic hash function in combination with a secret key. It ensures that both the data (message) and its origin (authenticity) are verified.

## Components

- **Hash Function**: A one-way function that produces a fixed-size output (hash) from an input (message). Common hash functions include SHA-256, SHA-1, and MD5.
- **Secret Key**: A private key used to generate and verify the HMAC. It should be kept confidential.
- **Message**: The data or payload that is being protected by HMAC.

## How HMAC Works

1. **Key Padding**: If the secret key is shorter than the block size of the hash function, it is padded. If it is longer, it is hashed to reduce its length.
2. **Inner Hash Calculation**: Combine the padded key with the message and compute the hash. This step involves XORing the key with a specific value and then hashing the result concatenated with the message.
3. **Outer Hash Calculation**: Combine the padded key with a second specific value, hash the result concatenated with the inner hash, and produce the final HMAC.

More specifically, HMAC is defined as:
$$ \text{HMAC}_K(M) = \text{H} \left( (K' \oplus \text{opad}) \Vert \text{H}((K' \oplus \text{ipad}) \Vert \text{M} \right) $$
where:
- $H$ is a cryptographic hash function.
- $M$ is the message.
- $K$ is the secret key.
- $K'$ is a block-sized key derived from the secret key $K$.
- $\text{opad}$ is the block-sized outer padding.
- $\text{ipad}$ is the block-sized inner padding.
- $\Vert$ denotes concatenation.
