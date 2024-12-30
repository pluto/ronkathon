# Digital Signature Algorithms (DSA)

## Introduction

**What are digital signatures?** 

Just like its name, **Digital Signatures** are digital analogs of physical signatures. For example, when you want to write a cheque you have to "sign" it for authentication purposes. But think about how you would do the same over the internet. 
Here is where **Digital Signatures** come into the picture. Just like physical signatures, digital signatures provide *authenticity*. Like how physical signatures on a cheque provide
a way to "verify" the identity of a signer.
Digital signatures also provide integrity. That is, they provide a mechanism to detect unauthorized modification.
Digital signatures also have another nice property: non-repudiation. Once a signer signs a message or a document, they cannot deny having done so.

In conclusion, **Digital Signatures** have the following properties:
1. Integrity
2. Authenticity
3. Non-repudiation

**How does a digital signature scheme look like?**

Digital signature schemes consists of three algorithms **Gen**, **Sign**, **Verify**, such that:

1. The key generation algorithm, $Gen$ which takes in the security parameter $1^n$ and outputs public key, $pk$ and private key, $sk$.
2. The signing algorithm $Sign$ takes as input the keys and a message and outputs a signature.
3. The verification algorithm $Verify$, takes as input the public key, a message, and a signature. 
It outputs bit 1 if the signature is valid for the given message and public key, otherwise 0.

**How is a digital signature scheme used?** 

To explain how digital signature schemes are used, let's take the example of two people, Bobby and Alex.
Bobby is the one whose signature is required, so Bobby will run the $Gen(1^n)$ algorithm to obtain, $pk, sk$. 
Then, the public key, $pk$, is publicized as belonging to Bobby. This way it can be verified that $pk$ actually belongs to Bobby. This one of the critical parts of a secure digital signature scheme. 
You can read more on this here: [Public key infrastructure](https://en.wikipedia.org/wiki/Public_key_infrastructure)

![](./keygen.gif)

Now when Alex sends a message(document, contract, etc.), $m$, for Bobby to sign, they compute the signature, $s$ as, $s\leftarrow Sign(sk,m)$ and sents $s$ to Alex or any other party who wants to take a look.
Now, any party who wants to see if Bobby signed the document or not, applies the verification algorithm using the public key as $Verify(pk,m,s)$.

![](./sign_and_verify.gif)

## References

1. "Introduction to Modern Cryptography" by Jonathan Katz and Yehuda Lindell


