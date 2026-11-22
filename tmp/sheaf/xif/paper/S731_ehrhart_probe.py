import sympy as sp
p=sp.Integer(5); c=sp.Rational(1,2); d=2
N=sp.symbols('N', positive=True, integer=True); t=sp.symbols('t', positive=True)
# p-adic fractional lattice F(c)=p^{-c} Z_p in rank 1: Haar measure p^{-c}
# rank d: p^{-d c}
for rank in (1,2):
    meas=sp.Integer(p)**(-rank*c)
    logmeas=sp.simplify(sp.log(meas))
    print("rank",rank,"c",c,"Haar=",meas,"log=",logmeas)
# Ehrhart of interval [0,N] and cube [0,N]^d
L1=N*t+1
L2=sp.expand((N*t+1)**2)
print("Ehrhart interval:",sp.factor(L1),"leading coeff:",sp.LC(sp.Poly(L1,t)))
print("Ehrhart square:",sp.expand(L2),"leading coeff:",sp.LC(sp.Poly(L2,t)))
# A fixed rank-1 fractional lattice region p^{-c} Z_p is not a bounded polytope;
# its Haar log is index log, independent of N.
print("Haar log rank1:", sp.simplify(sp.log(p**(-c))))
print("Haar log rank2:", sp.simplify(sp.log(p**(-2*c))))
# If one artificially takes t copies, Haar scales by t, log adds log t, not Ehrhart count.
print("t copies rank1 log:", sp.simplify(sp.log(t*p**(-c))))
print("Ehrhart t interval:", sp.expand(N*t+1))
