
import sympy as sp
t, T = sp.symbols('t T')
D = 2 * 3**2 * 5**2 * 7**2 * 27721
print("D =", D, sp.factorint(D))
A = -sp.Rational(3145728,33958225)*t**2 - sp.Rational(2876416,6237225)*t - sp.Rational(14425,55442)
f = 768*t**3 + 2176*t**2 + 400*t + 625
g = t**3 + sp.Rational(61,64)*t**2 - sp.Rational(125,64)*t
p = 463856467968*t**3 + 3973952045056*t**2 + 1991485440000*t + 6153500390625
q1 = -(12524124635136*t**3 + 79751150567424*t**2 - 83360885866496*t - 1012427556339675)/9515710442487800081671875
q2 = -(12524124635136*t**3 + 79751150567424*t**2 + 170840063183104*t - 659223575628975)/7308065619830630462724000000
As = sp.expand(A.subs(t, D*T))
fs = sp.expand(f.subs(t, As))
ps = sp.expand(p.subs(t, D*T))
q1s = sp.expand(q1.subs(t, D*T))
q2s = sp.expand(q2.subs(t, D*T))
gs = sp.expand(g.subs(t, As))
print("A_scaled:", sp.factor(As))
print("p_scaled:", sp.factor(ps))
print("q1_scaled:", sp.factor(q1s))
print("q2_scaled:", sp.factor(q2s))
print("f(A) - p*q1 ==0:", sp.expand(fs - ps*q1s)==0)
print("g(A)-D*T - p*q2 ==0:", sp.expand(gs - D*T - ps*q2s)==0)
# print integer coefficients
for name, poly in [("A",As),("p",ps),("q1",q1s),("q2",q2s)]:
    P = sp.Poly(poly, T)
    print(name, "deg", P.degree(), "coeffs", [sp.Rational(c) for c in P.all_coeffs()])
PY