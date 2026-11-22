
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
for n in [4]:
    a,b,c,d,e,f,p=(psi(n-1,x,y),psi(n,x,y),psi(n+1,x,y),psi(n-2,x,y),psi(n+2,x,y),psi(n-3,x,y),psi(2,x,y))
    g=psi(2*n-2,x,y); h=psi(2*n,x,y)
    Xm1=x*a*a-b*d; Xn=x*b*b-c*a
    u=Xm1/a**2; xn=Xn/b**2
    print("a b c d e f p g h",a,b,c,d,e,f,p,g,h)
    print("Xm1",Xm1,"Xn",Xn,"u",u,"xn",xn,"x",x)
    print("x-xn",x-xn,"c*a/b2",c*a/b**2,"eq",x-xn==c*a/b**2)
    print("u-x",u-x,"-bd/a2",-b*d/a**2,"eq",u-x==-b*d/a**2)
    print("u-xn",u-xn,"(c a2 - b3 d)/(a b2)",(c*a**2-b**3*d)/(a*b**2),"eq",u-xn==(c*a**2-b**3*d)/(a*b**2))
    num = g/a**4*(x-xn) - p*(u-xn)
    print("num",num,"den",u-x,"quot",num/(u-x))
    # manual terms
    t1=g/a**4*(x-xn); t2=p*(u-xn)
    print("t1",t1,"g c/(a3 b2)",g*c/(a**3*b**2),"eq",t1==g*c/(a**3*b**2))
    print("t2",t2,"p(c a2-b3d)/(a b2)",p*(c*a**2-b**3*d)/(a*b**2),"eq",t2==p*(c*a**2-b**3*d)/(a*b**2))
    print("quot formula", (-g*c + a*p*(c*a**2-b**3*d))/(a*b**3*d), "eq", num/(u-x)==(-g*c + a*p*(c*a**2-b**3*d))/(a*b**3*d))
    simp=(-g*c + a*p*(c*a**2-b**3*d))/(a*b**3*d)
    print("simp with g sub", ( - (a*(d*d*c-f*b*b)/p)*c + a*p*(c*a**2-b**3*d))/(a*b**3*d))
    print("target", h/b**4)
