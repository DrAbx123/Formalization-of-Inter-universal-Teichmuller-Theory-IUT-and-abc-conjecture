
import sympy as sp
from fractions import Fraction
coeffs = [463856467968, 3973952045056, 1991485440000, 6153500390625]
for c in coeffs:
    print(c, sp.factorint(c))
print("leading/1024 =", sp.Rational(463856467968,1024))
# monic polynomial: divide by leading coeff
# h = y^6 + (3973952045056/463856467968) y^4 + ... 
for c in coeffs[1:]:
    print(sp.Rational(c, coeffs[0]))
# check if coefficients after dividing by leading are nice
PY