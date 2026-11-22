
import cmath, math
from sympy import Rational, simplify, prime, isprime

def check(l):
    lp = (l-1)//2
    S = sum(j*j for j in range(1, lp+1))
    S_formula = l*(l*l-1)//24
    C = Rational(S, 2*l*lp)
    C_formula = Rational(l+1, 24)
    P = Rational(S, 2*l)
    P_formula = Rational(l*l-1, 48)
    G = P/lp
    H = Rational(1, 2*l)
    ratio = C/H
    return lp, S, S_formula, C, C_formula, P, P_formula, G, H, ratio

print("l  l*  S  S_formula  C  C_formula  P  G  H  ratio  C<=1")
for l in [5,7,11,13,17,19,23,29,31,37]:
    lp,S,Sf,C,Cf,P,Pf,G,H,ratio = check(l)
    print(f"{l:3d} {lp:3d} {S:5d} {Sf:5d}  {C} {Cf}  {P} {G} {H} {ratio}  {C<=1}")

print()
print("Gauss sums G(a;2l) numerically: check odd=0, even nonzero |G|^2=4l, a=0: 2l")
for l in [5,7,11,13,23,29]:
    N=2*l
    vals=[]
    for a in range(N):
        s=sum(cmath.exp(2j*math.pi*a*j*j/N) for j in range(N))
        vals.append(abs(s)**2)
    oddmax=max(vals[a] for a in range(N) if a%2==1)
    even_nonzero=[vals[a] for a in range(2,N,2)]
    print(f"l={l:2d} N={N:2d} odd max |G|^2={oddmax:.3e} even nonzero |G|^2 range=[{min(even_nonzero):.6f},{max(even_nonzero):.6f}] expect {4*l}  G(0)^2={vals[0]:.6f} expect {4*l*l}  sum_a |G|^2={sum(vals):.3f} expect {N*(4*l-2)}")

print()
print("mu_2l orbit average of (zeta^m q)^(j^2), q=0.37, symbolic sum over m: should be 0")
for l in [5,7,11]:
    N=2*l
    zeta=cmath.exp(2j*math.pi/N)
    for j in range(1,(l-1)//2+1):
        av=sum((zeta**m * 0.37)**(j*j) for m in range(N))/N
        print(f"l={l} j={j} |avg|={abs(av):.3e}")

print()
print("Second-moment criterion: average j^2 = l(l+1)/12 <= 2l iff l <= 23")
for l in [5,7,11,13,17,19,23,29]:
    avg2=Rational(l*(l+1),12)
    print(f"l={l:2d} avg j^2={avg2}  <=2l? {avg2 <= 2*l}")
