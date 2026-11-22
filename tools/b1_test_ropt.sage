from sage.all import *
E=EllipticCurve("11a1")
ic=E.isogeny_class()
print(type(ic), ic)
print([str(F.label()) for F in ic])
print([int(F.modular_degree()) for F in ic])
print(min(int(F.modular_degree()) for F in ic))
