import sympy as sp
x1,x2,y1,y2,a1,a2,a3,a4,a6 = sp.symbols('x1 x2 y1 y2 a1 a2 a3 a4 a6')
E1 = y1**2 + a1*x1*y1 + a3*y1 - (x1**3 + a2*x1**2 + a4*x1 + a6)
E2 = y2**2 + a1*x2*y2 + a3*y2 - (x2**3 + a2*x2**2 + a4*x2 + a6)
negY2 = -y2 - a1*x2 - a3
lp = (y1-y2)/(x1-x2)
lm = (y1-negY2)/(x1-x2)
S = lp**2+lm**2 + a1*(lp+lm) - 2*a2 - 2*(x1+x2)
num, den = sp.fraction(sp.together(S))
num = sp.expand(num)
print("den:", sp.factor(den))
G = sp.groebner([E1,E2], y1,y2,x1,x2,a1,a2,a3,a4,a6, order='lex')
rem = G.reduce(num)[1]
print("remainder w.r.t groebner:", sp.factor(rem))
