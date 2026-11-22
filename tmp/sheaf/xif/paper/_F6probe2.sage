from sage.libs.pari import pari
pari.allocatemem(8*1024*1024*1024)
E = EllipticCurve([0,0,1,-1,0])
R.<x> = QQ[]
K.<i> = NumberField(x^2+1)
EK = E.change_ring(K)
print("start F6 field simplify=False", flush=True)
F6 = EK.division_field(6, simplify=False)
print("F6 degree", F6.degree(), flush=True)
print("F6 disc", F6.discriminant().factor(), flush=True)
print("start torsion basis", flush=True)
B = EK.change_ring(F6).torsion_basis(6)
print("basis len", len(B), flush=True)
for P in B: print("P", P, flush=True)
