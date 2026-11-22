#!/usr/bin/env python3
"""A3 numerical support (route C A3): Belyi integrals, Legendre period, triples."""
import math, json, csv, heapq
import numpy as np
from fractions import Fraction
from sympy import factorint, binomial

OUT_CSV = "coord/a3_support.csv"

# ---------- Belyi ----------
def beta(z):
    return 4*z/(1+z)**2

def iterate(z,n):
    for _ in range(n):
        z=beta(z)
    return z

def I_r(n,r,N=20000):
    th=np.linspace(0,2*np.pi,N,endpoint=False)
    z=r*np.exp(1j*th)
    vals=np.array([iterate(zz,n) for zz in z])
    pos=np.maximum(np.log(np.abs(vals)),0.0)
    return float(np.trapezoid(pos,th)/(2*np.pi))

belyi=[]
for n in range(1,7):
    belyi.append({"n":n,"deriv0":4**n,"I_099":I_r(n,0.99),"I_0999":I_r(n,0.999)})

# ---------- Legendre ----------
a=[]
for n in range(0,301):
    a.append(int(binomial(2*n,n))**2)
ratios=[a[n+1]/a[n] for n in range(len(a)-1)]
legendre={"R_inf":"1/16","ratio_last":ratios[-1],"error_last":abs(ratios[-1]-16),
          "ratio_at_n100":ratios[100],"ratio_at_n300":ratios[-1]}

# ---------- triples ----------
LIM=3000
spf=list(range(LIM+1))
for i in range(2,int(LIM**0.5)+1):
    if spf[i]==i:
        for j in range(i*i,LIM+1,i):
            if spf[j]==j: spf[j]=i

def rad(n):
    if n>LIM:
        return int(math.prod(factorint(n).keys()))
    out=1
    while n>1:
        p=spf[n]; out*=p
        while n%p==0: n//=p
    return out

def bad_primes(n):
    f=factorint(n); out=[]
    for p in f:
        out.append(int(p))
    return sorted(out)

def padic_abs(frac,p):
    num=frac.numerator; den=frac.denominator
    v=0
    while num%p==0: v+=1; num//=p
    while den%p==0: v-=1; den//=p
    return Fraction(1, p**v) if v>=0 else Fraction(p**(-v),1)

def record(kind,idx,a,b,c,quality=None):
    S=sorted(set(bad_primes(a))|set(bad_primes(b))|set(bad_primes(c)))
    u=Fraction(a,c)
    uabs={str(p): padic_abs(u,p) for p in S}
    bad_padic=[p for p in S if uabs[str(p)] >= 1]
    Sex=[p for p in S if p>3]
    return {
        "kind":kind,"id":idx,"a":a,"b":b,"c":c,
        "quality":quality,
        "u":str(u),
        "u_float":float(u),
        "rad_abc":rad(a)*rad(b)*rad(c),
        "bad_primes":";".join(map(str,S)),
        "S_excess_>3":";".join(map(str,Sex)),
        "admissible_odd":all(p%2==1 for p in S),
        "admissible_padic":len(bad_padic)==0,
        "padic_bad_primes":";".join(map(str,bad_padic)),
        "u_p_abs":json.dumps({k:str(v) for k,v in uabs.items()}),
        "min_u_p_abs":str(min(uabs.values())),
        "max_u_p_abs":str(max(uabs.values())),
    }

rows=[]
for k in range(1,61):
    a=1; b=3**k-1; c=3**k
    rows.append(record("family_3",f"k{k}",a,b,c))

# high-quality triples from small scan
best=[]
for a in range(1,1501):
    for b in range(a+1,2001-a):
        c=a+b
        if math.gcd(a,b)!=1: continue
        r=rad(a)*rad(b)*rad(c)
        q=math.log(c)/math.log(r)
        heapq.heappush(best,(q,a,b,c))
        if len(best)>200: heapq.heappop(best)
tops=sorted(best,reverse=True)[:20]
for i,(q,a,b,c) in enumerate(tops,1):
    rows.append(record("high_quality",f"HQ{i}",a,b,c,q))

with open(OUT_CSV,"w",newline="") as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0].keys()))
    w.writeheader(); w.writerows(rows)

print(json.dumps({"n_rows":len(rows),"n_family":60,"n_hq":20,
                  "belyi":belyi,"legendre":legendre,
                  "high_quality_top":tops[:5],
                  "csv":OUT_CSV},indent=1))
