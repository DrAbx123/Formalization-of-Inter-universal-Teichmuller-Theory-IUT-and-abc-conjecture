
import sympy as sp
y = sp.symbols('y')
h = 463856467968*y**6 + 3973952045056*y**4 + 1991485440000*y**2 + 6153500390625
print("factor over Q(sqrt-3):")
print(sp.factor(h, extension=sp.sqrt(-3)))
print("factor over Q(sqrt-3) alt:")
print(sp.factor(h, extension=sp.I*sp.sqrt(3)))
PY