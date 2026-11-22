
import sympy as sp
y = sp.symbols('y')
H = 463856467968*y**6 + 3973952045056*y**4 + 1991485440000*y**2 + 6153500390625
Hp = sp.diff(H,y)
print("H'", Hp)
g, a, b = sp.gcdex(sp.Poly(H,y,domain=sp.QQ), sp.Poly(Hp,y,domain=sp.QQ), y)
print("gcd", g)
print("a deg", sp.degree(a,y), "b deg", sp.degree(b,y))
print("a", a)
print("b", b)
print("check", sp.expand(a*H + b*Hp))
PY