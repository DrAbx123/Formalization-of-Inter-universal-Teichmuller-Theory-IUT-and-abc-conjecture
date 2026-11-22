
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
x,y=Fr(3),Fr(6)
for n in range(3,8):
    a,b,c,d,e,f,p=(psi(n-1,x,y),psi(n,x,y),psi(n+1,x,y),psi(n-2,x,y),psi(n+2,x,y),psi(n-3,x,y),psi(2,x,y))
    g=psi(2*n-2,x,y)
    print(n, "gp",g*p, "d2ac-fab2", d*d*a*c-f*a*b*b, "eq", g*p==d*d*a*c-f*a*b*b)
    print("   even n formula rhs alt a*d2c - f*a*b2", a*(d*d*c-f*b*b))
