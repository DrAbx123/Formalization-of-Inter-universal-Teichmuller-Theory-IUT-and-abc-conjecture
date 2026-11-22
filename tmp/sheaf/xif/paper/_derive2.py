import sympy as sp
x,y,a4,a6 = sp.symbols('x y a4 a6')
E = y**2 - (x**3 + a4*x + a6)
# short Weierstrass, b2=0,b4=2a4,b6=4a6,b8=-a4^2
psi2 = 2*y
pre4 = 2*x**6 + 10*a4*x**4 + 40*a6*x**3 - 10*a4**2*x**2 - 8*a4*a6*x + 2*a4**3 - 16*a6**2
psi4 = pre4*psi2
# doubling: x2 = (x^4 - b4 x^2 - 2 b6 x - b8)/(4x^3+b2 x^2+2b4 x+b6)
b2=0; b4=2*a4; b6=4*a6; b8=-a4**2
x2 = (x**4 - b4*x**2 - 2*b6*x - b8)/(4*x**3 + b2*x**2 + 2*b4*x + b6)
# slope tangent for short: (3x^2+a4)/(2y)
lam = (3*x**2+a4)/(2*y)
y2 = -y + lam*(x - x2)   # y2 = -y - lam*(x2-x) = -y + lam*(x-x2); since line y=lam(X-x)+y; at x2, y2=lam(x2-x)+y, negated
w2 = 2*y2
expr = sp.together(w2*psi2**4 - psi4)
print(sp.factor(sp.simplify(expr)))
# reduce mod E
num, den = sp.fraction(expr)
print("num mod E:", sp.rem(sp.expand(num), E, y))
