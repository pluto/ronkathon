# Define a finite field, our `PlutoField` which is
# a field of 101 elements (101 being prime).
F = GF(101)
print(F)

# Generate primitive element
primitive_element = F.primitive_element()
print("The primitive element is: ", primitive_element)

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
assert omega_n ^ n == 1
print(omega_n, "^", n, " = ", omega_n ^ n)
######################################################################

# extension field of degree 2
Ft.<t> = F[]

# irreducible  element: t^2-2
P = Ft(t ^ 2 - 2)
assert P.is_irreducible()

F_2 = GF(101 ^ 2, name="t", modulus=P)
print("extension field:", F_2, "of order:", F_2.order())

# Primitive element
f_2_primitive_element = F_2.primitive_element()
print("Primitive element of F_2:", f_2_primitive_element, f_2_primitive_element.order())

# 100th root of unity
F_2_order = F_2.order()
root_of_unity_order = 100
quotient = (F_2_order-1)//root_of_unity_order

f_2_omega_n = f_2_primitive_element ^ quotient
print("The", root_of_unity_order, "th root of unity of extension field is: ", f_2_omega_n)

######################################################################

