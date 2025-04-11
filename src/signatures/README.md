# Lamport Signatures

Lamport signatures are a one-time use digital signature scheme invented by Leslie Lamport . Unlike most common signature schemes , Lamport signatures are believed to be secure against attacks from quantum computers, making them a candidate for post-quantum cryptography.

## How Lamport Signatures Work

The security of Lamport signatures relies solely on the security of cryptographic hash functions, specifically on their one-way (preimage resistance) property.

### Key Generation

1. For each bit position in the hash digest :
   - Generate two random values 
   - This gives us 512 random values total for the private key
   
2. The public key consists of the hash of each random value:
   - Hash each of the 512 values
   - The public key is these 512 hash values

### Signing a Message

1. Hash the message to produce a 256-bit digest
2. For each bit position in the digest:
   - If the bit is 0, reveal the first random value from the corresponding pair
   - If the bit is 1, reveal the second random value
3. The signature consists of these 256 revealed values

### Verifying a Signature

1. Hash the message to produce the same 256-bit digest
2. For each bit position in the digest:
   - If the bit is 0, hash the revealed value and check if it matches the first hash in the public key pair
   - If the bit is 1, hash the revealed value and check if it matches the second hash in the public key pair
3. The signature is valid only if all 256 hash checks pass

## Security Considerations

### One-Time Use

**Critical**: Each private key must be used exactly once. Reusing a private key for multiple signatures can compromise security by revealing enough of the private key for an attacker to forge signatures.

### Size Trade-offs

Lamport signatures are quite large:
- Private key: 512 × 256 bits = 16KB
- Public key: 512 × 256 bits = 16KB  
- Signature: 256 × 256 bits = 8KB

This is significantly larger than conventional signature schemes like ECDSA, which can fit in a few hundred bits.

### Quantum Resistance

The security of Lamport signatures relies on the one-way property of hash functions, which is believed to be resistant to quantum computer attacks. This contrasts with schemes based on integer factorization or discrete logarithms , which can be broken by Shor's algorithm running on a quantum computer.

