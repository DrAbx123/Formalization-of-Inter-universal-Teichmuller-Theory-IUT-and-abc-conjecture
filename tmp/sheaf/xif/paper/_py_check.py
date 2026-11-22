
from fractions import Fraction as Fr

a1=a2=a3=a4=Fr(0); a6=Fr(1)
b2=a1*a1+4*a2; b4=2*a4+a1*a3; b6=a3*a3+4*a6; b8=a1*a1*a6+4*a2*a6-a1*a3*a4+a2*a3*a3-a4*a4

def psi_val(n, x, y):
    memo={0:Fr(0),1:Fr(1),2:2*y+a1*x+a3,
          3:3*x**4+b2*x**3+3*b4*x**2+3*b6*x+b8}
    # psi4 = psi2 * prePsi4
    pre4 = 2*x**6 + b2*x**5 + 5*b4*x**4 + 10*b6*x**3 + 10*b8*x**2 + (b2*b8-b4*b6)*x + (b4*b8-b6*b6)
    memo[4]=memo[2]*pre4
    def rec(k):
        if k in memo: return memo[k]
        if k<0:
            r=-rec(-k)
        elif k%2==1:
            m=(k-1)//2
            r=rec(m+2)*rec(m)**3-rec(m-1)*rec(m+1)**3
        else:
            m=k//2
            r=(rec(m-1)**2*rec(m)*rec(m+2)-rec(m-2)*rec(m)*rec(m+1)**2)/rec(2)
        memo[k]=r; return r
    return rec(n)

def Phi_val(n,x,y):
    return x*psi_val(n,x,y)**2 - psi_val(n+1,x,y)*psi_val(n-1,x,y)

def negY(x,y): return -y-a1*x-a3
def w(x,y): return y-negY(x,y)
def add(P,Q):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2:
        if y1==negY(x2,y2): return None
        lam=(3*x1*x1+2*a2*x1+a4-a1*y1)/(y1-negY(x1,y1))
    else:
        lam=(y1-y2)/(x1-x2)
    x3=lam*lam+a1*lam-a2-x1-x2
    y3=negY(x3, lam*(x3-x1)+y1)
    return (x3,y3)

def mul(n,P):
    if n==0: return None
    if n<0:
        Q=mul(-n,P); return None if Q is None else (Q[0],negY(Q[0],Q[1]))
    R=None; Q=P
    while n:
        if n&1: R=add(R,Q)
        Q=add(Q,Q); n>>=1
    return R

x0=Fr(0); y0=Fr(1); P=(x0,y0)
for n in range(1,11):
    Q=mul(n,P); p=psi_val(n,x0,y0)
    if Q is None:
        print(n,"infinity"); continue
    wv=w(*Q); wf=psi_val(2*n,x0,y0)/p**4
    xf=Phi_val(n,x0,y0)/p**2
    print(n, "xmatch", Q[0]==xf, "wmatch", wv==wf, "psi",p)
    if not (Q[0]==xf and wv==wf):
        print("  x",Q[0],xf,"w",wv,wf)
