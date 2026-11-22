
import sympy as sp
x,z = sp.symbols('x z')
f = 768*x**3 + 2176*x**2 + 400*x + 625
g = x**3 + sp.Rational(61,64)*x**2 - sp.Rational(125,64)*x
for c in [1,2,3,4,5,6,7,8,9,10]:
    expr = -12*c**2*(z-x)**2 - ((z-x)**2 - g - 3*c**2)**2
    res = sp.Poly(sp.expand(sp.resultant(f, expr, x)), z)
    fac = sp.factor_list(res.as_expr())
    degs = [(sp.Poly(q,z).degree(), m) for q,m in fac[1]]
    print("c=",c,"totaldeg",res.degree(),"factors",degs)
PY