#!/usr/bin/env python3
"""A1007: LP on exact-e corrected local terms (coord/c1_local_terms_e_exact.jsonl)."""
import json, math, csv, collections
import numpy as np
from scipy.optimize import linprog
BINS=[(2,5),(5,10),(10,20),(20,50),(50,100),(100,200),(200,500),(500,1000),(1000,2000)]
def binidx(p):
    for i,(lo,hi) in enumerate(BINS):
        if lo<=p<hi: return i
    return len(BINS)-1
terms=collections.defaultdict(list)
for line in open("coord/c1_local_terms_e_exact.jsonl"):
    r=json.loads(line); terms[(r["N"],r["label"])].append(r)
rows=[]
for k,rs in terms.items():
    arch=sum(r["arch"] for r in rs); H=sum(r["H_p"] for r in rs); Ind=sum(r["Ind2_p"] for r in rs); T=sum(r["T_p"] for r in rs)
    posb=[0.0]*len(BINS); negb=[0.0]*len(BINS)
    for r in rs:
        net=r["H_p"]+r["Ind2_p"]-r["T_p"]
        if net>=0: posb[binidx(int(r["p"]))]+=net
        else: negb[binidx(int(r["p"]))]+=-net
    rows.append(dict(N=k[0],label=k[1],M=sum(r["H_p"]+r["Ind2_p"]-r["T_p"] for r in rs),
                     arch=arch,H=H,Ind=Ind,T=T,posnet=sum(posb),negabs=sum(negb),posb=posb,
                     admissible=rs[0]["admissible"]))
def getx(r):
    d={"const":1.0,"arch":r["arch"],"posnet":r["posnet"],"H":r["H"],"Ind":r["Ind"],"T":r["T"],"negabs":r["negabs"]}
    for i in range(len(BINS)): d[f"posbin{i}"]=r["posb"][i]
    return d
def solve(rows,names):
    F=np.array([[getx(r)[n] for n in names] for r in rows]); y=np.array([r["M"] for r in rows]); n,m=F.shape
    c=np.zeros(m+1); c[-1]=1
    A=np.vstack([np.hstack([F,-np.ones((n,1))]),np.hstack([-F,-np.ones((n,1))])]); b=np.concatenate([y,-y])
    res=linprog(c,A_ub=A,b_ub=b,bounds=[(0,None)]*m+[(0,None)],method="highs")
    lam=res.x[:m]; resid=F@lam-y; marg=res.ineqlin.marginals
    ar=np.abs(resid)
    return dict(t=float(res.fun),lam=lam.tolist(),max_abs=float(ar.max()),mean_abs=float(ar.mean()),
                rmse=float(np.sqrt((resid**2).mean())),
                cov1=float(np.mean(ar<=1e-6)),cov3=float(np.mean(ar<=1e-3)),cov01=float(np.mean(ar<=0.01)),
                dual_obj=float(np.dot(b,marg)),dual_sum=float(sum(marg)),
                dual_leq0=bool(all(x<=1e-9 for x in marg)),names=names,n=len(rows))
res=[]
clean=[r for r in rows if r["negabs"]<=1e-12]
names=["arch"]+[f"posbin{i}" for i in range(len(BINS))]
res.append({"tag":"clean_exact",**solve(clean,names)})
adb=[r for r in rows if r["admissible"]]
res.append({"tag":"admissible",**solve(adb,names)})
namesf=["const","arch","posnet","H","Ind","T"]+[f"posbin{i}" for i in range(len(BINS))]
res.append({"tag":"full",**solve(rows,namesf)})
for r in res:
    print(json.dumps(r,indent=1)[:4000])
json.dump(res,open("coord/decomp_lp_e_exact_results.json","w"),indent=1)
with open("coord/c1_local_features_e_exact.csv","w",newline="") as fh:
    w=csv.writer(fh);w.writerow(["N","label","M","admissible","arch","H","Ind","T","posnet","negabs"]+[f"posbin{i}" for i in range(len(BINS))])
    for r in rows: w.writerow([r["N"],r["label"],r["M"],r["admissible"],r["arch"],r["H"],r["Ind"],r["T"],r["posnet"],r["negabs"]]+r["posb"])
print("wrote coord/decomp_lp_e_exact_results.json, coord/c1_local_features_e_exact.csv",flush=True)
