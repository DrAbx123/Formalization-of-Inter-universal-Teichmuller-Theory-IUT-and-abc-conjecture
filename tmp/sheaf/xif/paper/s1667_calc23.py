
import sympy as sp
t = sp.symbols('t')
A = -sp.Rational(3145728,33958225)*t**2 - sp.Rational(2876416,6237225)*t - sp.Rational(14425,55442)
a = sp.Rational(-3145728,33958225); b = sp.Rational(-2876416,6237225); c = sp.Rational(-14425,55442)
for t0 in range(-200,201):
    v = sp.Rational(a*t0*t0 + b*t0 + c)
    if sp.denom(v)==1:
        print("t0",t0,"A(t0)",v)
        break
# choose D to clear a and b after shift: need a*D^2 integer, (2a t0 + b)*D integer
t0 = None
for s in range(-200,201):
    v = sp.Rational(a*s*s+b*s+c)
    if sp.denom(v)==1:
        t0=s; print("chosen t0",t0,"A",v); break
lin = 2*a*t0 + b
print("lin coeff", lin, sp.factorint(sp.denom(lin)))
print("quad coeff", a, sp.factorint(sp.denom(a)))
# D common denominator of a and lin: lcm of denoms
D = sp.lcm(sp.denom(a), sp.denom(lin))
D = int(D)
print("D",D, sp.factorint(D))
print("a D^2", a*D*D, "lin D", lin*D)
PY