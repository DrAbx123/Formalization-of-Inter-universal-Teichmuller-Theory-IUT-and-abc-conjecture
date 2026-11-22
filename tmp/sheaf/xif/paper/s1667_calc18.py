
import sympy as sp
y = sp.symbols('y')
H = 463856467968*y**6 + 3973952045056*y**4 + 1991485440000*y**2 + 6153500390625
Hp = sp.diff(H,y)
s,t,g = sp.gcdex(H,Hp,y)
print("g:", g)
print("s deg", sp.degree(s,y), "t deg", sp.degree(t,y))
print("s:", s)
print("t:", t)
print("check:", sp.expand(s*H + t*Hp) - g)
PY