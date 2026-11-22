
import sympy as sp
x,y,z = sp.symbols('x y z')
f = 768*x**3 + 2176*x**2 + 400*x + 625
g = x**3 + sp.Rational(61,64)*x**2 - sp.Rational(125,64)*x
h = sp.Poly(sp.expand(sp.resultant(f, y**2-g, x)), y)
print("h:", sp.factor(h.as_expr()))
for c in [1,2,3,4,5]:
    expr = (z-y)**2 + 3*c**2
    res = sp.Poly(sp.expand(sp.resultant(h.as_expr(), expr, y)), z)
    fac = sp.factor_list(res.as_expr())
    print("c=",c,"deg",res.degree(),"factors",[(sp.Poly(q,z).degree(),m) for q,m in fac[1]])
PY