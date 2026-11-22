
import sympy as sp
x,y,z = sp.symbols('x y z')
f = 768*x**3 + 2176*x**2 + 400*x + 625
g = x**3 + sp.Rational(61,64)*x**2 - sp.Rational(125,64)*x
res = sp.Poly(sp.expand(sp.resultant(f, y**2-g, x)), y)
print("deg in y:", res.degree())
fac = sp.factor_list(res.as_expr())
print([(sp.Poly(q,y).degree(), m) for q,m in fac[1]])
print("factor:", fac)
PY