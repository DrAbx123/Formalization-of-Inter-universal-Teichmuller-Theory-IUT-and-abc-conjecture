
import sympy as sp
y = sp.symbols('y')
H = 463856467968*y**6 + 3973952045056*y**4 + 1991485440000*y**2 + 6153500390625
Hp = sp.Poly(H, y)
for p in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]:
    fac = sp.factor_list(Hp.as_expr(), modulus=p)
    degs = [sp.Poly(q,y,modulus=p).degree() for q,m in fac[1]]
    if degs == [6]:
        print("irreducible mod", p)
        print("fac", fac)
    else:
        print("mod",p,"degs",degs)
PY