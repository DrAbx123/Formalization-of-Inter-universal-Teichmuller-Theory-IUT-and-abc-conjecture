# B1 exact integer-kernel minimisation, N<=1000 semistable Cremona
import json, math, csv, time
from sage.all import *
from sage.databases.cremona import CremonaDatabase
B=60; PL=[int(p) for p in primes(B)]
db=CremonaDatabase()
nf_cache={}
def nfs(N):
    if N not in nf_cache: nf_cache[N]=CuspForms(Gamma0(N),2).newforms(names='a')
    return nf_cache[N]
def is_int_coeff(v):
    try: int(v); return True
    except Exception: return False
def find_f(F,N,E):
    for i,f in enumerate(F):
        co=f.q_expansion(60); ok=True
        for p in PL:
            if N%p==0: continue
            try:
                if int(co[p])!=int(E.ap(p)): ok=False; break
            except Exception: ok=False; break
        if ok: return i
    return None
def int_rows(co,ps):
    if all(is_int_coeff(co[p]) for p in ps): return [[1]+[int(co[p]) for p in ps]]
    p0=next(p for p in ps if not is_int_coeff(co[p])); K=co[p0].parent(); one=K(1); deg=len(one.vector()); out=[]
    for k in range(deg):
        vals=[QQ(one.vector()[k])]+[QQ(K(co[p]).vector()[k]) for p in ps]
        den=1
        for x in vals: den=lcm(den,x.denominator())
        out.append([int(x*den) for x in vals])
    return out
def gcd_list(vals):
    g=0
    for v in vals: g=math.gcd(g,abs(int(v)))
    return g
def exact(N,lab,E):
    F=nfs(N); fi=find_f(F,N,E)
    if fi is None: return None
    ps=[p for p in PL if N%p!=0]
    co=F[fi].q_expansion(60); b=[1]+[int(co[p]) for p in ps]
    A=[]
    for gi,g in enumerate(F):
        if gi==fi: continue
        A.extend(int_rows(g.q_expansion(60),ps))
    if A: K=Matrix(ZZ,A).right_kernel_matrix()
    else: K=Matrix(ZZ,len(b),len(b),lambda i,j: 1 if i==j else 0)
    vals=[int(vector(ZZ,b)*vector(ZZ,K.row(i))) for i in range(K.nrows())] if K.nrows() else []
    g=gcd_list(vals)
    return dict(N=N,label=lab,r_f=int(E.congruence_number()),nforms=len(F),n_other=len(F)-1,ncols=len(b),rank=K.nrows(),min_abs=int(g),kernel_zero=(g==0))
out=[]; t0=time.time(); total=0
for N in range(1,1001):
    try: d=db.allcurves(N)
    except Exception as e: continue
    for lab,dat in sorted(d.items()):
        total+=1
        try:
            E=EllipticCurve(dat[0])
            if not E.is_semistable(): continue
            label=f"{N}{lab}"
            r=exact(N,label,E)
            if r: out.append(r)
        except Exception as e:
            print('ERR',N,lab,type(e).__name__,e,flush=True)
    if N%100==0: print('progress N',N,'total',total,'rows',len(out),'t',round(time.time()-t0,1),flush=True)
with open('coord/b1_exact_snf_1000.csv','w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(out[0].keys())); w.writeheader(); w.writerows(out)
print('done rows',len(out),'total curves',total,'elapsed',round(time.time()-t0,2))
