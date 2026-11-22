import json, math, csv, time
from sage.all import *
rows=json.load(open("coord/b1_curves_500.json"))[:30]
B=60; PL=[int(p) for p in primes(B)]
nf_cache={}
def nfs(N):
    if N not in nf_cache:
        nf_cache[N]=CuspForms(Gamma0(N),2).newforms(names='a')
    return nf_cache[N]
def find_f(F,N,E):
    for i,f in enumerate(F):
        co=f.q_expansion(60)
        ok=True
        for p in PL:
            if N%p==0: continue
            try:
                if int(co[p])!=int(E.ap(p)): ok=False; break
            except Exception:
                ok=False; break
        if ok: return i
    return None
def compute(row):
    N=int(row["N"]); lab=row["label"]; E=EllipticCurve(lab)
    F=nfs(N); fi=find_f(F,N,E)
    if fi is None: return {"label":lab,"N":N,"error":"no matching newform"}
    f=F[fi]; co=f.q_expansion(60); b=[1]+[int(co[p]) for p in PL if N%p!=0]
    # columns: constant + primes p<=B, p not | N
    ps=[p for p in PL if N%p!=0]
    A=[]
    for gi,g in enumerate(F):
        if gi==fi: continue
        cg=g.q_expansion(60)
        A.append([1]+[int(cg[p]) for p in ps])
    if A:
        M=Matrix(ZZ,A); K=M.right_kernel_matrix()
    else:
        K=Matrix(ZZ, len(b), len(b), lambda i,j: 1 if i==j else 0)
    if K.nrows()==0:
        g=0; vals=[]
    else:
        vals=[int(vector(ZZ,b)*vector(ZZ,K.row(i))) for i in range(K.nrows())]
        g=0
        for v in vals: g=math.gcd(g,abs(v))
    return {"N":N,"label":lab,"r_f":int(row["r_f"]),"nforms":len(F),"n_other":len(F)-1,"ncols":len(b),"kernel_rank":K.nrows(),"min_abs":int(g),"vals":vals[:10]}
for r in rows:
    try: print(compute(r),flush=True)
    except Exception as e: print("ERR",r["label"],type(e).__name__,e,flush=True)
