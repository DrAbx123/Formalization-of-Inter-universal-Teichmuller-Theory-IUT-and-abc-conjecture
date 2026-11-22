
import sympy as sp
y = sp.symbols('y')
H = 463856467968*y**6 + 3973952045056*y**4 + 1991485440000*y**2 + 6153500390625
Hp = sp.diff(H,y)
print("gcd:", sp.gcd(H,Hp))
print("factor H:", sp.factor(H))
print("disc H:", sp.factor(sp.discriminant(H,y)))
print("resultant:", sp.factor(sp.resultant(H,Hp,y)))
PY