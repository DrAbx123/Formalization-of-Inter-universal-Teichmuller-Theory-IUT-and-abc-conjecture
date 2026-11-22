import time
E=EllipticCurve([0,-1,1,-10,-20])
ps=prime_range(10000)
print("primes",len(ps))
t=time.time(); vals=[E.ap(p) for p in ps[:200]]; print("200",time.time()-t)
t=time.time(); vals=[E.ap(p) for p in ps]; print("all",time.time()-t)
