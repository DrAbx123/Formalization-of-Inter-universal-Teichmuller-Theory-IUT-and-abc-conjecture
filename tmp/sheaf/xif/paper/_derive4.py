import sympy as sp
x,a1,a2,a3,a4,a6 = sp.symbols('x a1 a2 a3 a4 a6')
w,A,B,C,D,E = sp.symbols('w A B C D E')
b2=a1**2+4*a2; b4=2*a4+a1*a3; b6=a3**2+4*a6
W = { -2:A, -1:B, 0:C, 1:D, 2:E }
def rel(m,k,r):
    vals = [m+k, m-k, m+r, m-r, k+r, k-r]
    if any(v not in W for v in vals): return None
    return sp.expand(W[m+k]*W[m-k]*W[r]**2 - (W[m+r]*W[m-r]*W[k]**2 - W[k+r]*W[k-r]*W[m]**2))
rels=set()
for m in range(-2,3):
  for k in range(-2,3):
    for r in [1,2]:
      rr=rel(m,k,r)
      if rr is not None and rr != 0: rels.add(rr)
rels=list(rels)
print("rels", len(rels))
Zn = x - D*B/C**2
Znm1 = x - C*A/B**2
Znp1 = x - E*C/D**2
N = lambda u,v: 2*u*v*(u+v)+b2*u*v+b4*(u+v)+b6
expr = sp.together(Znp1+Znm1 - N(Zn,x)/(Zn-x)**2)
num,den = sp.fraction(expr)
num=sp.expand(num)
# add relation w^2 = Psi2Sq(x)
Psi2Sq = 4*x**3+b2*x**2+2*b4*x+b6
rels2 = rels + [w**2-Psi2Sq]
G = sp.groebner(rels2, A,B,C,D,E,w, order='lex')
rem = G.reduce(num)[1]
print("remainder:", sp.factor(rem))
