# our prime modulus
F101 = IntegerModRing(101)

# A number 5 in our prime modulus, should be 5
print(IntegerMod(F101, 5))

# Should be 96
print(IntegerMod(F101, -5))

# should be 81
print(IntegerMod(F101, 1/5))

# should be 20
print(IntegerMod(F101, -1/5))

# should be 100
print(IntegerMod(F101, -1))

# Lets make our elliptic curve
E = EllipticCurve(F101, [0, 3])

# lets print out the points, notice they print (x,y,z) the difference between homogeneous points and affine points is that to use affine you just divide x,y by z.
# We can see here that for all points in the curve group z = 1 except the zero point at infinity. So for this field they are the same
print(E.points())

# Define polynomial ring
R.<X> = PolynomialRing(F101)

# Lets make an extension field
# niavely: we could pick x^2 + 1 but
# x^2 + 1 = x^2 + 100 = (x+10)(x-10) -> There is a root in the field
# lets pick x^2 + 2 which is irreducible in our field

# Extended polynomial ring
F2.<X> = GF(101**2, modulus = x^2 + 2)

# Curve group over polynomial ring
E2 = EllipticCurve(F2, [0, 3])
print(E2.points())

# G1 is the generator for E1
G1 = E(1,2)
print(G1)

# N is the order of the group E1
N = 17

# G2 is the generator for E2
G2 = E2([36, 31 *X])
print(G2)

# Now Lets generate the structured reference string (SRS),
# we will use the "random" number 2 for the example but in practice it should be strong random.
# a circuit with n gates requires an SRS with at least
# n + 5 elements as below
# We will let it be of length 9, pythagorean triple uses 4 gates
g1SRS = [(2**i)*G1 for i in range(7)]
print(g1SRS)

g2SRS = [(2**i)*G2 for i in range(2)]
print(g2SRS)


######################################################################
GF17 = GF(17)

coefs = [11, 11, 11, 1]
# 11 * g1_srs[0] + 11 * g1_srs[1] + 11 * g1_srs[2] + 1 * g1_srs[3]
muls  = [(coefs[i] * g1SRS[i]) for i in range(4)]
commitment = sum(muls)
print(commitment)

######################################################################
# weil and tate Pairings

k = 2
r = 17

a = E2.random_element()
b = E2.random_element()
c = E2.random_element()
a = (a.order()//17)*a
b = (b.order()//17)*b
c = (c.order()//17)*c
print("points", a, b, c)

tate_sage = a.tate_pairing(b, r, k)
print("tate pairing", tate_sage)

tate_1 = a.tate_pairing(b+c, r, k)
tate_2 = a.tate_pairing(b, r, k) * a.tate_pairing(c, r, k)
print(tate_1, tate_2)

weil_sage = a.weil_pairing(b, r)
print("weil", weil_sage)

######################################################################
