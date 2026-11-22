
import cmath, math
from sympy import Rational, isprime

def gauss(l, a):
    N=2*l
    return sum(cmath.exp(2j*math.pi*a*j*j/N) for j in range(N))

def eps(l):
    # G(1;l) = sqrt(l) if l=1 mod 4, i*sqrt(l) if l=3 mod 4
    return 1 if l%4==1 else 1j

def legendre(b,l):
    return 1 if pow(b%l,(l-1)//2,l)==1 else -1

print("Exact Gauss formula check: G(2b;2l) = 2*(b/l)*eps_l*sqrt(l), b != 0")
for l in [5,7,11,13,17,23,29]:
    for b in [1,2,3]:
        if b%l==0: continue
        g=gauss(l,2*b)
        pred=2*legendre(b,l)*eps(l)*math.sqrt(l)
        print(f"l={l:2d} b={b} G={g:.6f} pred={pred:.6f} diff={abs(g-pred):.2e}")

print()
print("mu_2l moment identity m_k = (1/2l) sum_m zeta^{mk} = 1 if 2l|k else 0")
for l in [5,7]:
    N=2*l; z=cmath.exp(2j*math.pi/N)
    for k in range(1,2*N+1):
        m=sum(z**(m*k) for m in range(N))/N
        if abs(m)>1e-9:
            print(f"l={l} k={k} m_k={m.real:.6f}{m.imag:+.6f}i (2l|k: {k%N==0})")
print("(no output above the first nonzero means all zeros; check k=2l,4l)")
for l in [5,7]:
    N=2*l; z=cmath.exp(2j*math.pi/N)
    for k in [N,2*N]:
        m=sum(z**(m*k) for m in range(N))/N
        print(f"l={l} k={k} m_k={m.real:.6f}{m.imag:+.6f}i")

print()
print("Variance of uniform label distribution j=1..l*:")
for l in [5,7,11,23,29]:
    lp=(l-1)//2
    mean=Rational(lp+1,2)
    avg2=Rational(l*(l+1),12)
    var=avg2-mean*mean
    print(f"l={l:2d} mean={mean} E[j^2]={avg2} Var={var}  Var/(2l)={var/Rational(2*l)}  E[j^2]/(2l)={avg2/Rational(2*l)}")
