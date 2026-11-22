
import sympy as sp
Y = sp.symbols('Y')
a = sp.Rational(118433,13824)
b = sp.Rational(4501875,1048576)
d = sp.Rational(227907421875,17179869184)
def poly_for_c(c):
    c = sp.Rational(c)
    return sp.expand(Y**6 + a/c**2*Y**4 + b/c**4*Y**2 + d/c**6)
for ea in range(0,15):
    for eb in range(0,8):
        c = 2**ea * 3**eb
        p = poly_for_c(c)
        coeffs = sp.Poly(p,Y).all_coeffs()
        if all(sp.denom(sp.Rational(co))==1 for co in coeffs):
            # check Eisenstein primes
            eis = []
            for pr in [2,3,5,7,11,13,17,19,23,29,31]:
                cc = [int(co) for co in coeffs]
                if cc[0]==1 and all(x % pr == 0 for x in cc[1:]) and (cc[-1] % (pr*pr) != 0):
                    eis.append(pr)
            print("c=",c,"coeffs=",coeffs,"eisenstein",eis)
PY