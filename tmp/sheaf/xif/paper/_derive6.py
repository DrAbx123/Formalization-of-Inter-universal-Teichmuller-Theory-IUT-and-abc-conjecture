import sympy as sp
x,a1,a2,a3,a4,a6 = sp.symbols('x a1 a2 a3 a4 a6')
w,A,B,C,D,E = sp.symbols('w A B C D E')
b2=a1**2+4*a2; b4=2*a4+a1*a3; b6=a3**2+4*a6
W = { -2:A, -1:B, 0:C, 1:D, 2:E }
def netrel(p,q,r,s):
    vals=[p+q+s,p-q,r+s,r,p+r+s,p-r,q+s,q,q+r+s,q-r,p+s,p]
    if any(v not in W for v in vals): return None
    e=sp.expand(W[p+q+s]*W[p-q]*W[r+s]*W[r] - W[p+r+s]*W[p-r]*W[q+s]*W[q] + W[q+r+s]*W[q-r]*W[p+s]*W[p])
    return (p,q,r,s,e)
rels=[]
for p in range(-3,4):
 for q in range(-3,4):
  for r in range(-3,4):
   for s in range(-3,4):
    rr=netrel(p,q,r,s)
    if rr and rr[4]!=0: rels.append(rr)
rels=list({r[4]:r for r in rels}.values())
Zn = x - D*B/C**2; Znm1 = x - C*A/B**2; Znp1 = x - E*C/D**2
N = lambda u,v: 2*u*v*(u+v)+b2*u*v+b4*(u+v)+b6
expr=sp.together(Znp1+Znm1 - N(Zn,x)/(Zn-x)**2); num=sp.fraction(expr)[0]
Psi2Sq=4*x**3+b2*x**2+2*b4*x+b6
base=[w**2-Psi2Sq]
def rem(tuples):
    rs=[t[4] for t in tuples]
    G=sp.groebner(rs+base,A,B,C,D,E,w,order='lex')
    return sp.expand(G.reduce(num)[1])
cur=rels[:]
print("initial",len(cur))
changed=True
while changed:
    changed=False
    for r in list(cur):
        test=[q for q in cur if q is not r]
        if rem(test)==0:
            cur=test; changed=True; break
print("needed",len(cur))
for t in cur: print((t[0],t[1],t[2],t[3]), ":", sp.factor(t[4]))
