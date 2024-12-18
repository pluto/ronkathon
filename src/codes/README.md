# Codes
In some cryptographic protocols, we need to do encoding and decoding.
Specifically, we implement the Reed-Solomon encoding and decoding in this module.

## Reed-Solomon Encoding
The Reed-Solomon encoding is a kind of error-correcting code that works by oversampling the input data and adding redundant symbols to the input data.
Our specific case takes a `Message<K, P>` that is a list of `K` field elements for the `PrimeField<P>`. 
We can then call the `encode::<N>()` method on the `Message<K, P>` to get a `Codeword<N, K, P>` that is an encoded version of message with redundancy added.

First, we create a polynomial in `Monomial` form from our message by having each element of the message be a coefficient of the polynomial.
To do this encoding, we get the `N`th root of unity in the field and evaluate the polynomial at each of the powers of that root of unity.
We then store these evaluations in the codeword along with the point at which they were evaluated.
In effect, this is putting  polynomial into the Lagrange basis where the node points are the `N`th roots of unity.

That is to say, we have a message $M = (m_0, m_1, \ldots, m_{K-1})$ and we encode it into a codeword $C = (c_0, c_1, \ldots, c_{N-1})$ where:
$$
\begin{align*}  
c_i &= \sum_{j=0}^{K-1} m_j \cdot \omega^{ij}
\end{align*}
$$
where $\omega$ is the `N`th root of unity.

## Reed-Solomon Decoding
Given we have a `Codeword<M, K, P>`, we can call the `decode()` method to get a `Message<K, P>` that is the original message so long as the assertion `M>=N` holds.
Doing the decoding now just requires us to go from the Lagrange basis back to the monomial basis.
For example, for a degree 2 polynomial, we have:
$$
\begin{align*}
\ell_0(x) &= \frac{(x - \omega)(x - \omega^2)}{(1 - \omega)(1 - \omega^2)}\\
\ell_1(x) &= \frac{(x - 1)(x - \omega^2)}{(\omega - 1)(\omega - \omega^2)}\\
\ell_2(x) &= \frac{(x - 1)(x - \omega)}{(\omega^2- 1)(\omega^2 - \omega)}
\end{align*}
$$
where $\ell_i(x)$ is the $i$th Lagrange basis polynomial.

Effectively, we just need to expand out our codeword in this basis and collect terms:
$$
\begin{align*}
c_0 \ell_0(x) + c_1 \ell_1(x) + c_2 \ell_2(x) &= m_0 + m_1 x + m_2 x^2
\end{align*}
$$
where $m_i$ are the coefficients of the original message.
Note that we can pick any `N` points of the codeword to do this expansion, but we need at least `K` points to get the original message back.
For now, we just assume the code is the same length for the example.

Multiplying out the left hand side we get the constant coefficient as:
$$
\begin{align*}
m_0 = \frac{c_0 \omega \omega^2}{(\omega - 1)(\omega^2 - 1)} + \frac{c_1 (1) \omega^2}{(1 - \omega)(\omega^2 - \omega)} + \frac{c_2 (1) \omega}{(1 - \omega^2)(\omega - \omega^2)} 
\end{align*}
$$
the linear coefficient as:
$$
\begin{align*}
-m_1 = \frac{c_0 (\omega + \omega^2)}{(\omega - 1)(\omega^2 - 1)} + \frac{c_1 (1 + \omega^2)}{(1 - \omega)(\omega^2 - \omega)} + \frac{c_2 (1 + \omega)}{(1 - \omega^2)(\omega - \omega^2)} 
\end{align*}
$$
the quadratic coefficient as:
$$
\begin{align*}
m_2 = \frac{c_0 }{(\omega - 1)(\omega^2 - 1)} + \frac{c_1 
}{(1 - \omega)(\omega^2 - \omega)} + \frac{c_2}{(1 - \omega^2)(\omega - \omega^2)} 
\end{align*}
$$

This process was generalized in the `decode()` method.
