
import sympy as sp
y = sp.symbols('y')
h = 463856467968*y**6 + 3973952045056*y**4 + 1991485440000*y**2 + 6153500390625
# try galois group
try:
    from sympy.polys.numberfields.galoisgroups import galois_group
    G = galois_group(sp.Poly(h,y))
    print("galois group:", G)
except Exception as e:
    print("galois error:", repr(e))
# factor over algebraic extension root
try:
    r = sp.CRootOf(h, 0)
    print("CRootOf:", r)
    print("factor over Q(y):", sp.factor(h, extension=r))
except Exception as e:
    print("factor error:", repr(e))
PY