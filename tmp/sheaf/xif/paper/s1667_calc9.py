
import sympy as sp
t = sp.symbols('t')
f = 768*sp.Symbol('x')**3 + 2176*sp.Symbol('x')**2 + 400*sp.Symbol('x') + 625
x = sp.Symbol('x')
g = x**3 + sp.Rational(61,64)*x**2 - sp.Rational(125,64)*x
# p(t) = 463856467968 t^3 + 3973952045056 t^2 + 1991485440000 t + 6153500390625
p = 463856467968*t**3 + 3973952045056*t**2 + 1991485440000*t + 6153500390625
# find A(t)=a t^2+b t+c with g(A) = t mod p and f(A)=0 mod p
a,b,c = sp.symbols('a b c')
A = a*t**2+b*t+c
# g(A) - t mod p
rem_g = sp.rem(sp.expand(g.subs(x,A) - t), p, t)
rem_f = sp.rem(sp.expand(f.subs(x,A)), p, t)
print("rem_g coeffs:", sp.Poly(rem_g,t).all_coeffs())
print("rem_f coeffs:", sp.Poly(rem_f,t).all_coeffs())
sol = sp.solve([sp.Poly(rem_g,t).coeff_monomial(t**k) for k in range(3)] + [sp.Poly(rem_f,t).coeff_monomial(t**k) for k in range(3)], [a,b,c], dict=True)
print("solutions:", sol)
for S in sol:
    A2 = sp.expand(A.subs(S))
    print("A=",A2)
    remg2 = sp.rem(sp.expand(g.subs(x,A2)-t), p, t)
    remf2 = sp.rem(sp.expand(f.subs(x,A2)), p, t)
    print("remg2", sp.Poly(remg2,t).all_coeffs())
    print("remf2", sp.Poly(remf2,t).all_coeffs())
    print("factor remf2/p:", sp.simplify(remf2/p))
PY