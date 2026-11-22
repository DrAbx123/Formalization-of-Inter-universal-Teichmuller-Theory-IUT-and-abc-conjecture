from sage.all import *
K.<i> = QuadraticField(-1)
E = EllipticCurve([0,0,1,-1,0]).change_ring(K)
print("start")
F = E.division_field(6, simplify=False)
print("deg", F.degree())
print("disc", F.discriminant().factor())