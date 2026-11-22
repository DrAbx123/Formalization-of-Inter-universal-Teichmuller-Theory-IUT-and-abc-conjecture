
import sympy as sp
x,z,t = sp.symbols('x z t')
f = 768*x**3 + 2176*x**2 + 400*x + 625
g = x**3 + sp.Rational(61,64)*x**2 - sp.Rational(125,64)*x
res = sp.resultant(f, (z-x)**2 - g, x)
res = sp.Poly(sp.expand(res), z)
print("resultant:", sp.factor(res.as_expr()))
print("degree:", res.degree())
print("factor list:", sp.factor_list(res.as_expr()))
print("disc f:", sp.discriminant(f,x), sp.factorint(sp.discriminant(f,x)))
# minpoly of alpha + sqrt(-3)
d = sp.sqrt(-3)
res2 = sp.resultant(f, (z-x)**2 + 3, x)
res2 = sp.Poly(sp.expand(res2), z)
print("alpha+sqrt(-3) resultant:", sp.factor(res2.as_expr()), "deg", res2.degree())
PY