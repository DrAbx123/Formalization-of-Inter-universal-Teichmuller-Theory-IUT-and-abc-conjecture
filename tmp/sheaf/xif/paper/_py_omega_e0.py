
import sympy as sp
a,b,c,g,Bv,Ev,Fv = sp.symbols('a b c g Bv Ev Fv', nonzero=True)
e = Ev*b**3 - c*a**3
fg = b**2*a*Fv - c*a*Ev**2
dg = c**2*b*Ev - Bv*b*a**2
g2e = b**2*c*Fv - a**2*Bv*Ev
E0g = fg*b**4*c + dg*a**4*c - g2e*b**4*a + dg*e*a
print(sp.factor(sp.expand(E0g)))
