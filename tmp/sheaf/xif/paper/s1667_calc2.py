
import sympy as sp
x,z = sp.symbols('x z')
f = 768*x**3 + 2176*x**2 + 400*x + 625
g = x**3 + sp.Rational(61,64)*x**2 - sp.Rational(125,64)*x
expr = -12*(z-x)**2 - ((z-x)**2 - g - 3)**2
res = sp.resultant(f, expr, x)
res = sp.Poly(sp.expand(res), z)
print("deg:", res.degree())
fac = sp.factor(res.as_expr())
print("factor:", fac)
print("factor_list lengths:", [(sp.Poly(q,z).degree(), m) for q,m in sp.factor_list(res.as_expr())[1]])
PY