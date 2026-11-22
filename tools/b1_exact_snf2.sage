# A980: exact SNF with same-level newforms + all proper-divisor oldforms
# usage: sage tools/b1_exact_snf2.sage <NMAX> <PMAX> <json|cremona> <outcsv>
import sys, json, math, csv, time
from sage.all import *
from sage.databases.cremona import CremonaDatabase
NMAX=int(sys.argv[1]); PMAX=int(sys.argv[2]); SRC=sys.argv[3]; OUT=sys.argv[4]
PL=[int(p) for p in primes(PMAX)]
nf_cache={}
def nfs(N):
    if N not in nf_cache: nf_cache[N]=CuspForms(Gamma0(N),2).newforms(names='a')
    return nf_cache[N]
def is_int_coeff(v):
    try: int(v); return True
    except Exception: return False
def find_f(F,N,E):
    for i,f in enumerate(F):
        co=f.q_expansion(PMAX+2); ok=True
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
ropt_cache={}
def ropt(E):
    ic=list(E.isogeny_class())
    key=tuple(sorted(str(F.label()) for F in ic))
    if key not in ropt_cache:
        ropt_cache[key]=min(int(F.modular_degree()) for F in ic)
    return ropt_cache[key]
def exact(N,lab,E):
    F=nfs(N); fi=find_f(F,N,E)
    if fi is None: return {"N":N,"label":lab,"error":"no matching newform"}
    ps=[p for p in PL if N%p!=0]
    co=F[fi].q_expansion(PMAX+2); b=[1]+[int(co[p]) for p in ps]
    A=[]; n_old=0
    # same-level other newforms
    for gi,g in enumerate(F):
        if gi==fi: continue
        A.extend(int_rows(g.q_expansion(PMAX+2),ps))
    # oldforms: all newforms at proper divisor levels
    for M in divisors(N):
        if M==N: continue
        for h in nfs(M):
            A.extend(int_rows(h.q_expansion(PMAX+2),ps)); n_old+=1
    if A: K=Matrix(ZZ,A).right_kernel_matrix()
    else: K=Matrix(ZZ,len(b),len(b),lambda i,j: 1 if i==j else 0)
    vals=[int(vector(ZZ,b)*vector(ZZ,K.row(i))) for i in range(K.nrows())] if K.nrows() else []
    g=gcd_list(vals)
    r=ropt(E)
    return dict(N=N,label=lab,r_f_opt=int(r),nforms=len(F),n_same_other=len(F)-1,n_oldforms=n_old,ncols=len(b),rank=K.nrows(),min_abs=int(g),valid_div=(int(g)>0 and int(r)>0 and int(g)%int(r)==0),valid_ge=(int(g)>=int(r)),kernel_zero=(g==0))
# input rows
if SRC=="json":
    src=json.load(open("coord/b1_curves_500.json"))
    tasks=[(int(r["N"]),r["label"]) for r in src]
else:
    db=CremonaDatabase(); tasks=[]
    for N in range(1,NMAX+1):
        try: d=db.allcurves(N)
        except Exception: continue
        for lab,dat in sorted(d.items()):
            try:
                E=EllipticCurve(dat[0])
                if E.is_semistable(): tasks.append((N,str(N)+lab))
            except Exception: pass
out=[]; t0=time.time()
for i,(N,lab) in enumerate(tasks):
    try:
        E=EllipticCurve(lab); r=exact(N,lab,E); out.append(r)
    except Exception as e:
        print("ERR",lab,type(e).__name__,e,flush=True)
    if (i+1)%100==0: print("progress",i+1,"/",len(tasks),round(time.time()-t0,1),flush=True)
with open(OUT,"w",newline="") as f:
    w=csv.DictWriter(f,fieldnames=list(out[0].keys())); w.writeheader(); w.writerows(out)
print("done",len(out),"elapsed",round(time.time()-t0,2),"out",OUT)
