
import sympy as sp
a,b,c,g,Bv,Ev,Fv = sp.symbols('a b c g Bv Ev Fv', nonzero=True)
# solve R1,R2,R3 for f,d,e
f = (b**2*a*Fv - c*a*Ev**2)/g
d = (c**2*b*Ev - Bv*b*a**2)/g
e = Ev*b**3 - c*a**3
T = f/a**4 - (-d/b**4 + (g-d/b**4)*(e/(a**3*c)))
T = sp.together(T)
num, den = sp.fraction(sp.cancel(T))
print("num:", sp.factor(num))
print("den:", sp.factor(den))
# R4 after substitution
R4 = b**2*c*Fv - a**2*Bv*Ev - g**2*e
print("R4:", sp.factor(R4))
# express num in terms of R4
print("num/R4:", sp.simplify(num/R4))
