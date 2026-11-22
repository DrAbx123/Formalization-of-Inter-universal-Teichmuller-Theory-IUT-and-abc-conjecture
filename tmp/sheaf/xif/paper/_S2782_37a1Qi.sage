from sage.all import *
K.<i> = QuadraticField(-1)
E = EllipticCurve([0,0,1,-1,0]).change_ring(K)
for ld in E.local_data():
    print([a for a in dir(ld) if not a.startswith("_")])
    print(ld)