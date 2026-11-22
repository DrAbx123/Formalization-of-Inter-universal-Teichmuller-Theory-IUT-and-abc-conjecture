
from fractions import Fraction as Fr
a1=a2=a3=a4=Fr(0); a6=Fr(3)
b2=a1*a1+4*a2; b4=2*a4+a1*a3; b6=a3*a3+4*a6; b8=a1*a1*a6+4*a2*a6-a1*a3*a4+a2*a3*a3-a4*a4
def psi(n,x,y):
    memo={0:Fr(0),1:Fr(1),2:2*y+a1*x+a3,3:3*x**4+b2*x**3+3*b4*x**2+3*b6*x+b8}
    pre4=2*x**6+b2*x**5+5*b4*x**4+10*b6*x**3+10*b8*x**2+(b2*b8-b4*b6)*x+(b4*b8-b6*b6)
    memo[4]=memo[2]*pre4
    def rec(k):
        if k in memo: return memo[k]
        if k<0: r=-rec(-k)
        elif k%2:
            m=(k-1)//2; r=rec(m+2)*rec(m)**3-rec(m-1)*rec(m+1)**3
        else:
            m=k//2; r=(rec(m-1)**2*rec(m)*rec(m+2)-rec(m-2)*rec(m)*rec(m+1)**2)/rec(2)
        memo[k]=r; return r
    return rec(n)
def negY(x,y): return -y-a1*x-a3
def add(P,Q):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2:
        if y1==negY(x2,y2): return None
        lam=(3*x1*x1+2*a2*x1+a4-a1*y1)/(y1-negY(x1,y1))
    else: lam=(y1-y2)/(x1-x2)
    x3=lam*lam+a1*lam-a2-x1-x2
    y3=negY(x3, lam*(x3-x1)+y1)
    return (x3,y3)
def mul(n,P):
    if n==0: return None
    if n<0:
        Q=mul(-n,P); return None if Q is None else (Q[0],negY(Q[0],Q[1]))
    R=None;Q=P
    while n:
        if n&1:R=add(R,Q)
        Q=add(Q,Q);n>>=1
    return R
x,y=Fr(3),Fr(6); P=(x,y)
for n in range(3,9):
    a,b,c,d,e,f,p=(psi(n-1,x,y),psi(n,x,y),psi(n+1,x,y),psi(n-2,x,y),psi(n+2,x,y),psi(n-3,x,y),psi(2,x,y))
    g=psi(2*n-2,x,y); h=psi(2*n,x,y)
    Xm1=x*a*a-b*d; Xn=x*b*b-c*a
    u=Xm1/a**2; xn=Xn/b**2
    wn=(g/a**4*(x-xn)-p*(u-xn))/(u-x)
    Wn=mul(n,P)
    print(n,"wn",wn,"h/b4",h/b**4,"eq",wn==h/b**4,"wactual", (Wn[1]-negY(*Wn)) if Wn else None)
    # also check my simplification formula
    simp=(a*a*c*p*p-b**3*d*p*p-c*c*d*d+c*f*b*b)/(b**3*d*p)
    print("   simp",simp,"eq",simp==h/b**4)
