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
omega_m = primitive_element^quotient
print("The ", m, "th root of unity is: ", omega_m)

# Check that this is actually a root of unity:
assert omega_m^m == 1
print(omega_m, "^", m, " = ", omega_m^m)
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
omega_n = primitive_element^quotient
print("The ", n, "th root of unity is: ", omega_n)

# Check that this is actually a root of unity:
assert omega_n^n == 1
print(omega_n, "^", n, " = ", omega_n^n)
######################################################################