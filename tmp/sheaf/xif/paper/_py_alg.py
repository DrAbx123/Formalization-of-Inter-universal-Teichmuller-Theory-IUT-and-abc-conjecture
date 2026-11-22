
import sympy as sp
x,a,b,c,d,e,f,g,h,p = sp.symbols('x a b c d e f g h p', nonzero=True)
Xm1 = x*a**2 - b*d
Xn = x*b**2 - c*a
u = Xm1/a**2
xn = Xn/b**2
wnm1 = g/a**4
w1 = p
expr = (wnm1*(x - xn) - w1*(u - xn))/(u - x)
print("raw expr:"); print(sp.factor(sp.simplify(expr)))
# substitute g = a*(d**2*c - f*b**2)/p and h = b*(a**2*e - d*c**2)/p
gsub = a*(d**2*c - f*b**2)/p
hsub = b*(a**2*e - d*c**2)/p
E = sp.simplify(expr.subs(g, gsub))
target = hsub/b**4
diff = sp.factor(sp.simplify(E - target))
print("diff after substitutions:"); print(diff)
# try reduce using p^2 relation? maybe need p = psi2 and relation? Print numerator/denominator
num,den = sp.fraction(sp.cancel(E))
print("num:", sp.factor(num))
print("den:", sp.factor(den))
