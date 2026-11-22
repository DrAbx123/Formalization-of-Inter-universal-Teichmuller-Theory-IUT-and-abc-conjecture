import sympy as sp
x,a1,a2,a3,a4,a6 = sp.symbols('x a1 a2 a3 a4 a6')
w,A,B,C,D,E = sp.symbols('w A B C D E')
b2=a1**2+4*a2; b4=2*a4+a1*a3; b6=a3**2+4*a6
W = { -2:A, -1:B, 0:C, 1:D, 2:E }
def netrel(p,q,r,s):
    vals=[p+q+s,p-q,r+s,r,p+r+s,p-r,q+s,q,q+r+s,q-r,p+s,p]
    if any(v not in W for v in vals): return None
    return sp.expand(W[p+q+s]*W[p-q]*W[r+s]*W[r] - W[p+r+s]*W[p-r]*W[q+s]*W[q] + W[q+r+s]*W[q-r]*W[p+s]*W[p])
rels=set()
R=range(-3,4)
for p in R:
 for q in R:
  for r in R:
   for s in R:
    rr=netrel(p,q,r,s)
    if rr is not None and rr!=0: rels.add(rr)
rels=list(rels)
print("net rels",len(rels))
Zn = x - D*B/C**2
Znm1 = x - C*A/B**2
Znp1 = x - E*C/D**2
N = lambda u,v: 2*u*v*(u+v)+b2*u*v+b4*(u+v)+b6
expr = sp.together(Znp1+Znm1 - N(Zn,x)/(Zn-x)**2)
num,den=sp.fraction(expr); num=sp.expand(num)
Psi2Sq = 4*x**3+b2*x**2+2*b4*x+b6
rels2=rels+[w**2-Psi2Sq]
G=sp.groebner(rels2,A,B,C,D,E,w,order='lex')
rem=G.reduce(num)[1]
print("remainder:", sp.factor(rem))
