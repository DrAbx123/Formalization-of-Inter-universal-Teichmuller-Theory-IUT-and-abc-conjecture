
import sympy as sp
t = sp.symbols('t')
p = 463856467968*t**3 + 3973952045056*t**2 + 1991485440000*t + 6153500390625
pp = sp.diff(p,t)
print("p'", pp)
a,b = sp.symbols('a b')
# solve a*p + b*pp = 1 with deg a <=1, deg b <=2
# polynomial division extended gcd
g, s, t2 = sp.gcdex(p, pp, t)
print("gcd", g)
print("s", s)
print("t", t2)
print("check", sp.expand(s*p + t2*pp))
PY