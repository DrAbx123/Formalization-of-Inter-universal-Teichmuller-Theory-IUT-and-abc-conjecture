
import sympy as sp
t = sp.symbols('t')
x = sp.symbols('x')
f = 768*x**3 + 2176*x**2 + 400*x + 625
g = x**3 + sp.Rational(61,64)*x**2 - sp.Rational(125,64)*x
p = 463856467968*t**3 + 3973952045056*t**2 + 1991485440000*t + 6153500390625
A = -sp.Rational(3145728,33958225)*t**2 - sp.Rational(2876416,6237225)*t - sp.Rational(14425,55442)
q1 = sp.div(sp.expand(f.subs(x,A)), p, t)[0]
q2 = sp.div(sp.expand(g.subs(x,A)-t), p, t)[0]
print("q1:", sp.factor(q1))
print("q2:", sp.factor(q2))
print("q1 degree", sp.Poly(q1,t).degree(), "q2 degree", sp.Poly(q2,t).degree())
print("q1 * p == f(A)?", sp.expand(q1*p - f.subs(x,A))==0)
print("q2 * p == g(A)-t?", sp.expand(q2*p - (g.subs(x,A)-t))==0)
PY