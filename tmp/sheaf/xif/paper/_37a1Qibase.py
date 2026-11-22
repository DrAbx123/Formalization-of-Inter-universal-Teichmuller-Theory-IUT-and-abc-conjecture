E=EllipticCurve([0,0,1,-1,0])
K=QuadraticField(-1,'i')
i=K.gen()
EK=E.change_ring(K)
for P in K.primes_above(2)+K.primes_above(37):
    print("P",P, flush=True)
    try: print(EK.local_data(P), flush=True)
    except Exception as e: print("err",type(e).__name__,e, flush=True)
