import sympy as sp
x,a1,a2,a3,a4,a6 = sp.symbols('x a1 a2 a3 a4 a6')
w,A,B,C,D,E,c = sp.symbols('w A B C D E c')
b2 = a1**2+4*a2; b4=2*a4+a1*a3; b6=a3**2+4*a6
N = lambda u,v: 2*u*v*(u+v)+b2*u*v+b4*(u+v)+b6
xn = x - D*B/C**2
xnm1 = x - C*A/B**2
xnp1 = x - E*C/D**2
R = xnp1+xnm1
RHS = N(xn,x)/(xn-x)**2
F = E*A - (D*B*w**2 - c*C**2)
Psi2Sq = 4*x**3+b2*x**2+2*b4*x+b6
# also w^2 = Psi2Sq(x), c = prePsi3(x); treat w,c independent but w^2 relation
diff = sp.together(R-RHS)
num,den = sp.fraction(sp.together(diff))
num = sp.expand(num)
# compute numerator expression in E via F
E_expr = (D*B*w**2 - c*C**2)/A
numE = sp.expand(num.subs(E,E_expr))
# reduce w^2 -> Psi2Sq
numE = sp.expand(numE.subs(w**2,Psi2Sq))
print("after F and w^2:", sp.factor(numE))
