# Digital Signature Algorithms (DSA)

### What are digital signatures?

Like its name, **Digital Signatures** are digital analogs of physical signatures. For example, when you want to write a cheque you have to "sign" it for authentication purposes. But think about how you would do the same over the internet. 
Here is where **Digital Signatures** come into the picture. 

**Digital Signatures** have the following properties:
1. **Authenticity**: Just like physical signatures, digital signatures provide a way to verify the identity of a signer.
2. **Integrity**: Digital signatures provide a mechanism to detect unauthorized modification to a message.
3. **Non-repudiation**: Digital signatures have a nice property that once a signer signs a message, they cannot deny having done so.

### How does a digital signature scheme look like?

Digital signature schemes consists of three algorithms $\text{Gen, Sign, Verify}$, such that:

1. The key generation algorithm, $\text{Gen}$ which takes in the security parameter $n$ and outputs public key, $\text{pk}$ and private key, $\text{sk}$.
2. The signing algorithm $\text{Sign}$ takes as input the keys and a message and outputs a signature.
3. The verification algorithm $\text{Verify}$, takes as input the public key, a message, and a signature. 
It outputs bit 1 if the signature is valid for the given message and public key, otherwise 0.

### How is a digital signature scheme used?

To explain how digital signature schemes are used, let's take the example of two people, Bobby and Alex.
Bobby is the one whose signature is required, so Bobby will run the $\text{Gen(n)}$ algorithm to obtain, $\text{pk, sk}$. 
Then, the public key, $\text{pk}$, is publicized as belonging to Bobby. This not only provides authentication but also ensures non-repudiation. This one of the critical parts of a secure digital signature scheme. 
You can read more on this here: [Public key infrastructure](https://en.wikipedia.org/wiki/Public_key_infrastructure)

![](../../assets/keygen.gif)

Now when Alex sends a message(document, contract, etc.), $m$, for Bobby to sign, they compute the signature, $s$ as, $s\leftarrow\text{Sign(sk,m)}$ and sents $s$ to Alex or any other party who wants to take a look.
Now, any party who wants to see if Bobby signed the document or not, applies the verification algorithm using the public key as $\text{Verify(pk,m,s)}$. Thus Alex or any other party can be sure of the authenicity of
the signature as well as the integrity of the message.

![](../../assets/sign_and_verify.gif)

### When is a signature scheme said to be secure?

A digital signature scheme is said to be secure if an adversary is unable to generate a forgery, that is, a message (not previously signed) and a valid signature for a fixed public key, in any case.

### Examples of digital signature scheme

1. Elliptic Curve Digital Signature Scheme(ECDSA)
2. Edwards-Curve Digital Signature Scheme(EdDSA)

## References

1. "Introduction to Modern Cryptography" by Jonathan Katz and Yehuda Lindell
2. [Digital Signatures](https://asecuritysite.com/signatures)


