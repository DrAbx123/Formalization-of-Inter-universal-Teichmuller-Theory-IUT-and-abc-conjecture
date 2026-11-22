E=EllipticCurve([0,-1,0,-142,701])
print("global torsion",E.torsion_order())
for p in [2,7]:
    try:
        print("p",p,"local",E.local_data(p), flush=True)
    except Exception as e:
        print("p",p,"error",e, flush=True)
