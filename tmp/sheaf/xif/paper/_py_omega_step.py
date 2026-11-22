
from fractions import Fraction as Fr
import sympy as sp
a,b,c,d,e,f,g,Bv,Ev,Fv = sp.symbols('a b c d e f g Bv Ev Fv')
R1 = f*g - (b**2*a*Fv - c*a*Ev**2)
R2 = d*g - (c**2*b*Ev - Bv*b*a**2)
R3 = e - (Ev*b**3 - c*a**3)
R4 = b**2*c*Fv - a**2*Bv*Ev - g**2*e
T = f/a**4 - (-d/b**4 + (g-d/b**4)*(e/(a**3*c)))
num = sp.together(T).as_numer_denom()[0]
print("target numerator:", sp.factor(num))
G = sp.groebner([R1,R2,R3,R4], a,b,c,d,e,f,g,Bv,Ev,Fv, order='lex')
rem = G.reduce(num)[1]
print("remainder:", sp.factor(rem))
# numeric check with actual psi values (their naming) on curve y^2=x^3+2x+3, P=(3,6)
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
for n in range(3,7):
    a_=psi(n,x,y); b_=psi(n-1,x,y); c_=psi(n-2,x,y); g_=psi(2,x,y)
    d_=psi(2*n-2,x,y); e_=psi(2*n-1,x,y); f_=psi(2*n,x,y)
    Bv_=psi(n-3,x,y); Ev_=psi(n+1,x,y); Fv_=psi(n+2,x,y)
    lhs=f_/a_**4; rhs=-d_/b_**4+(g_-d_/b_**4)*(e_/(a_**3*c_))
    print(n, lhs==rhs, "R1",f_*g_==b_**2*a_*Fv_-c_*a_*Ev_**2,"R2",d_*g_==c_**2*b_*Ev_-Bv_*b_*a_**2,"R3",e_==Ev_*b_**3-c_*a_**3,"R4", b_**2*c_*Fv_-a_**2*Bv_*Ev_-g_**2*e_)
