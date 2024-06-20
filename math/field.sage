# Define a finite field, our `GF101` which is
# a field of 101 elements (101 being prime).
F = GF(101)
print(F)

# Generate primitive element
primitive_element = F.primitive_element()
print("The primitive element is: ", primitive_element)

# Quadratic Residues
elements = [F(i) for i in range(1,101)]
quadratic_residues = [x^2 for x in elements]
print("The quadratic residues are: ", sorted(set(quadratic_residues)))

######################################################################
# Let's find a mth root of unity (for m = 5)
# First, check that m divides 101 - 1 = 100
m = 5
assert (101 - 1) % m == 0
quotient = (101 - 1) // m
print("The quotient is: ", quotient)

# Find a primitive root of unity using the formula:
# omega = primitive_element^quotient
omega_m = primitive_element ^ quotient
print("The ", m, "th root of unity is: ", omega_m)

# Check that this is actually a root of unity:
assert omega_m ^ m == 1
print(omega_m, "^", m, " = ", omega_m ^ m)
######################################################################

######################################################################
# Let's find a mth root of unity (for n = 25)
# First, check that m divides 101 - 1 = 100
n = 25
assert (101 - 1) % n == 0
quotient = (101 - 1) // n
print("The quotient is: ", quotient)

# Find a primitive root of unity using the formula:
# omega = primitive_element^quotient
omega_n = primitive_element ^ quotient
print("The", n, "th root of unity is: ", omega_n)

# Check that this is actually a root of unity:
assert omega_n^n == 1
print(omega_n, "^", n, " = ", omega_n^n)
######################################################################

######################################################################
# Let's find a mth root of unity (for l = 2)
# First, check that m divides 101 - 1 = 100
l = 2
assert (101 - 1) % l == 0
quotient = (101 - 1) // l
print("The quotient is: ", quotient)

# Find a primitive root of unity using the formula:
# omega = primitive_element^quotient
omega_l = primitive_element^quotient
print("The ", l, "th root of unity is: ", omega_l)

# Check that this is actually a root of unity:
assert omega_l^l == 1
print(omega_l, "^", l, " = ", omega_l^l)
assert omega_n ^ n == 1
print(omega_n, "^", n, " = ", omega_n ^ n)
######################################################################

# extension field of degree 2
Ft.<t> = F[]

# irreducible  element: t^2 + 2
P = Ft(t ^ 2 + 2)
assert P.is_irreducible()

F = GF(101)
Ft.<t> = F[]
P = Ft(t ^ 2 + 2)
F_2 = GF(101 ^ 2, name="t", modulus=P)
f_2_primitive_element = F_2.primitive_element()
assert f_2_primitive_element.multiplicative_order() == (101^2) -1
print("Primitive element of F_2:", f_2_primitive_element, f_2_primitive_element.multiplicative_order())

# 100th root of unity
F_2_order = F_2.order()
root_of_unity_order = 100
quotient = (F_2_order-1)//root_of_unity_order

f_2_omega_n = f_2_primitive_element ^ quotient
print("The", root_of_unity_order, "th root of unity of extension field is: ", f_2_omega_n)

######################################################################

# Define the field and elements for computation
F = GF(101)
Ft.<t> = F[]

# Define the polynomial for the extension field
P = Ft(t^2 + 2)
F_2 = GF(101^2, name="t", modulus=P)

# Define the elements 50 and 60t in the extension field
numerator = F_2(50)
denominator = F_2(62*t)

# Compute the division of 50 by 60t in the extension field
result = numerator / denominator
print("The division of 50 by 60t in the extension field is:", result)

######################################################################
# Binary field extensions

F = GF(2)
Ft.<t> = F[]
P = Ft(t^8+t^4+t^3+t+1)
F_2_8 = GF(2^8, name="t", modulus=P)
a = t^7+t^5 # 160
b = 1+t+t^2+t^4 # 23
a = F_2_8(a)
b = F_2_8(b)
print(a.additive_order(), (a*b).additive_order()) # 163()
a = set()
for point in F_2_8:
	a.add(point.additive_order())
one = F_2_8(0)
print("primitive element:", F_2_8.primitive_element().order(), a, one.order())
