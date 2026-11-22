from sympy import factorint
import time
for k in [10,20,30,40,50,60]:
    n=3**k-1; t=time.time(); f=factorint(n); print(k, len(f), time.time()-t, list(f.items())[:5])
