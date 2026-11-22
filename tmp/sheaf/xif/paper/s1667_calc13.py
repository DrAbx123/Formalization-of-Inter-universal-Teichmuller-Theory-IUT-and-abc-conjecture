
import sympy as sp
z = sp.symbols('z')
H = 463856467968*sp.Symbol('y')**6 + 3973952045056*sp.Symbol('y')**4 + 1991485440000*sp.Symbol('y')**2 + 6153500390625
y = sp.Symbol('y')
for a in range(-20,21):
  for b in range(1,21):
    c = sp.Rational(a,b)
    P = sp.Poly(sp.expand(H.subs(y, z+c)), z)
    coeffs = [int(co) for co in P.all_coeffs()]
    # primitive? content
    g = 0
    for co in coeffs: g = sp.gcd(g, abs(co))
    if g>1:
      coeffs = [co//g for co in coeffs]
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
      if coeffs[0] % p != 0 and all(co % p == 0 for co in coeffs[1:]) and coeffs[-1] % (p*p) != 0:
        print("shift c=",c,"prime",p,"poly",coeffs)
        raise SystemExit
print("none found")
PY