E=EllipticCurve([0,0,0,-1,0])
K=QuadraticField(-1, 'i')
i=K.gen()
EK=E.change_ring(K)
P=K.ideal(1+i)
print("P",P, flush=True)
for name, fn in [("minimal", lambda: EK.minimal_model(P)), ("local_data", lambda: EK.local_data(P)), ("tate", lambda: EK.tate_curve(P)), ("conductor", lambda: EK.conductor(P))]:
    try:
        print(name, fn(), flush=True)
    except Exception as e:
        print(name, "error", type(e).__name__, e, flush=True)
