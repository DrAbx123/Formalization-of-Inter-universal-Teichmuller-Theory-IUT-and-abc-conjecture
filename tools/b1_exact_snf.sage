# B1 exact integer-kernel SNF minimisation (A979)
import json, math, csv, time, sys
from sage.all import *
from sage.databases.cremona import CremonaDatabase

B=60
PL=[int(p) for p in primes(B)]
rows=json.load(open("coord/b1_curves_500.json"))
cert={}
for r in csv.DictReader(open("coord/b1_certificates.csv")):
    cert[(int(r["N"]),r["curve"])]=r
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

def is_int_coeff(v):
    try:
        int(v); return True
    except Exception:
        return False

def int_row_for_form(co, ps):
    # returns list of integer rows for one form (constant + ps)
    if all(is_int_coeff(co[p]) for p in ps):
        return [[1]+[int(co[p]) for p in ps]]
    p0=next(p for p in ps if not is_int_coeff(co[p]))
    K=co[p0].parent()
    one=K(1)
    deg=len(one.vector())
    rows=[]
    for k in range(deg):
        vals=[QQ(one.vector()[k])]+[QQ(K(co[p]).vector()[k]) for p in ps]
        den=1
        for x in vals: den=lcm(den, x.denominator())
        rows.append([int(x*den) for x in vals])
    return rows
def gcd_list(vals):
    g=0
    for v in vals: g=math.gcd(g,abs(int(v)))
    return g
def exact(row):
    N=int(row["N"]); lab=row["label"]; E=EllipticCurve(lab)
    F=nfs(N); fi=find_f(F,N,E)
    if fi is None: return None
    ps=[p for p in PL if N%p!=0]
    co=F[fi].q_expansion(60)
    b=[1]+[int(co[p]) for p in ps]
    A=[]
    for gi,g in enumerate(F):
        if gi==fi: continue
        cg=g.q_expansion(60)
        A.extend(int_row_for_form(cg, ps))
    if A:
        K=Matrix(ZZ,A).right_kernel_matrix()
    else:
        K=Matrix(ZZ, len(b), len(b), lambda i,j: 1 if i==j else 0)
    vals=[int(vector(ZZ,b)*vector(ZZ,K.row(i))) for i in range(K.nrows())] if K.nrows() else []
    g=gcd_list(vals)
    g2=0
    return dict(N=N,label=lab,r_f=int(row["r_f"]),deg_phi=int(row["deg_phi"]),
                nforms=len(F),n_other=len(F)-1,ncols=len(b),rank=K.nrows(),
                min_abs=int(g),min_abs_nc=int(g2),
                qp_found=(cert.get((N,lab),{}).get("found","")),
                qp_value=(cert.get((N,lab),{}).get("value","")),
                qp_type=(cert.get((N,lab),{}).get("type","")),
                kernel_zero=(g==0))
out=[]; t0=time.time()
for i,row in enumerate(rows):
    try:
        r=exact(row)
        if r: out.append(r)
    except Exception as e:
        print("ERR",row["label"],type(e).__name__,e,flush=True)
    if (i+1)%100==0: print("progress",i+1,"/",len(rows),round(time.time()-t0,1),flush=True)
with open("coord/b1_exact_snf_500.csv","w",newline="") as f:
    w=csv.DictWriter(f,fieldnames=list(out[0].keys())); w.writeheader(); w.writerows(out)
print("done",len(out),"elapsed",round(time.time()-t0,2))
