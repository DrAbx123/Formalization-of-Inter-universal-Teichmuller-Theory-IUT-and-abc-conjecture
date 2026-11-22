
import sympy as sp
z = sp.symbols('z')
y = sp.symbols('y')
H = 463856467968*y**6 + 3973952045056*y**4 + 1991485440000*y**2 + 6153500390625
primes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113]
found = 0
for b in range(1,13):
  for a in range(-2*b, 2*b+1):
    if sp.gcd(a,b)!=1: continue
    c = sp.Rational(a,b)
    P = sp.Poly(sp.expand(H.subs(y, z+c)), z)
    coeffs = [sp.Rational(co) for co in P.all_coeffs()]
    # clear denominators by multiplying by lcm of denominators
    L = 1
    for co in coeffs:
      L = sp.lcm(L, sp.denom(co))
    ints = [int(co*L) for co in coeffs]
    g = 0
    for co in ints: g = sp.gcd(g, abs(co))
    ints = [co//g for co in ints]
    for p in primes:
      if any(co % p != 0 for co in ints):
        fac = sp.factor_list(sp.Poly(sum(ints[i]*z**(len(ints)-1-i) for i in range(len(ints))), z, domain=sp.GF(p)))
        degs = [sp.Poly(q,z,modulus=p).degree() for q,m in fac[1]]
        if degs == [6]:
          print("FOUND c=",c,"prime",p,"ints",ints)
          found=1
          raise SystemExit
print("none found")
PY