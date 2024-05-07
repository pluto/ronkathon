# Define a finite field, our `GF101` which is 
# a field of 101 elements (101 being prime).
F = GF(101)

# Define the polynomial ring over GF(101)
R.<x> = PolynomialRing(F)

# Create the polynomials
a = 4*x^3 + 3*x^2 + 2*x^1 + 1
b = 9*x^4 + 8*x^3 + 7*x^2 + 6*x^1 + 5

# Perform polynomial division
q_ab, r_ab = a.quo_rem(b)

# Print the results
print("For a / b :")
print("Quotient:", q_ab)
print("Remainder:", r_ab)

# Perform polynomial division
q_ba, r_ba = b.quo_rem(a)

# Print the results
print("\nFor b / a :")
print("Quotient:", q_ba)
print("Remainder:", r_ba)

# Polynomials easy to do by hand
p = x^2 + 2*x + 1
q = x + 1

# Perform polynomial division
quot, rem = p.quo_rem(q)
print("\nFor p / q :")
print("Quotient:", quot)
print("Remainder:", rem)