
import sympy as sp
t = sp.symbols('t')
p = 463856467968*t**3 + 3973952045056*t**2 + 1991485440000*t + 6153500390625
pp = sp.diff(p,t)
print("gcd:", sp.gcd(p,pp))
print("factor p:", sp.factor(p))
print("disc:", sp.discriminant(p,t))
print("gcd QQ:", sp.gcd(sp.Poly(p,t,domain=sp.QQ), sp.Poly(pp,t,domain=sp.QQ)))
print("gcdex QQ:", sp.gcdex(sp.Poly(p,t,domain=sp.QQ), sp.Poly(pp,t,domain=sp.QQ), t))
PY