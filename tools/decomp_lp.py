#!/usr/bin/env python3
"""A991: LP decomposition search for the paper margin M over local nonnegative features.
Data: coord/c1_margin_v2.csv (N,label,nbad,M,admissible); model constants from
coord/c1_margin_corrected.csv used only to motivate feature names.
No Lean/Sage/WSL; pure Python (numpy/scipy)."""
import csv, math, json, sys
import numpy as np
from scipy.optimize import linprog

ARCH = math.log(math.sqrt(2.0) * math.pi)   # nonnegative constant ~1.4913

def factor_primes(n):
    ps=[]; d=2
    while d*d<=n:
        if n%d==0:
            ps.append(d)
            while n%d==0: n//=d
        d += 1 if d==2 else 2
    if n>1: ps.append(n)
    return ps

def features(N,nbad):
    ps=factor_primes(N)
    logN=math.log(N)
    tame=sum((1.0-1.0/p)*math.log(p) for p in ps)
    invp=sum(math.log(p)/p for p in ps)
    invsqrt=sum(math.log(p)/math.sqrt(p) for p in ps)
    return {
      "const":1.0,
      "logN":logN,
      "nbad":float(nbad),
      "tame":tame,
      "invp":invp,
      "invsqrt":invsqrt,
      "avg":logN/nbad,
      "nbad_arch":nbad*ARCH,
      "logN2":logN*logN,
      "nbad2":float(nbad*nbad),
      "cross":logN*nbad,
      "arch":ARCH,
    }

def build(rows,names):
    F=np.array([[features(int(r["N"]),int(r["nbad"]))[k] for k in names] for r in rows],dtype=float)
    y=np.array([float(r["M"]) for r in rows],dtype=float)
    return F,y

def lp_solve(F,y,names,reg=0.0):
    # variables [lambda_0..lambda_{m-1}, t]
    n,m=F.shape
    # min t (+ tiny sum lambda to break degeneracy)
    c=np.zeros(m+1); c[-1]=1.0
    if reg: c[:m]=reg
    A=[]; b=[]
    # F l - t <= y ; -F l - t <= -y
    A.append(np.hstack([F, -np.ones((n,1))])); b.append(y)
    A.append(np.hstack([-F, -np.ones((n,1))])); b.append(-y)
    A=np.vstack(A); b=np.concatenate(b)
    bounds=[(0,None)]*m+[(0,None)]
    res=linprog(c,A_ub=A,b_ub=b,bounds=bounds,method="highs")
    if not res.success: return None
    lam=res.x[:m]; t=float(res.x[-1]); resid=F@lam-y
    dual=res.ineqlin.marginals if hasattr(res,"ineqlin") and res.ineqlin is not None else None
    return {"lambda":lam.tolist(),"t":t,"resid":resid.tolist(),"dual":None if dual is None else [float(x) for x in dual],
            "objective":float(res.fun),"names":names}

def report(tag,rows,names):
    F,y=build(rows,names)
    r=lp_solve(F,y,names)
    if r is None: print(tag,"LP_FAIL",flush=True); return None
    resid=np.array(r["resid"]); absr=np.abs(resid)
    coverage=lambda tol: float(np.mean(absr<=tol))
    out={"tag":tag,"n":len(rows),"features":names,"lambda":r["lambda"],"t":r["t"],
         "objective":r["objective"],"max_abs_resid":float(absr.max()),
         "mean_abs_resid":float(absr.mean()),"rmse":float(np.sqrt(np.mean(resid**2))),
         "cov_1e-6":coverage(1e-6),"cov_1e-3":coverage(1e-3),"cov_0.01":coverage(0.01),
         "dual_norm":float(np.linalg.norm(r["dual"])) if r["dual"] else None,
         "dual_sign_ok":(all(x>=-1e-9 for x in r["dual"]) if r["dual"] else None)}
    print(json.dumps(out,indent=1)[:4000],flush=True)
    return out

if __name__=="__main__":
    rows=list(csv.DictReader(open("coord/c1_margin_v2.csv")))
    print("rows",len(rows),"admissible",sum(1 for r in rows if r["admissible"]=="True"),flush=True)
    allrows=rows
    adm=[r for r in rows if r["admissible"]=="True"]
    sets={
      "const":["const"],
      "agg":["const","logN","nbad","tame","invp","avg"],
      "agg2":["const","logN","nbad","tame","invp","invsqrt","avg","nbad_arch"],
      "poly":["const","logN","nbad","tame","invp","invsqrt","avg","nbad_arch","logN2","nbad2","cross","arch"],
    }
    results=[]
    for tag,names in sets.items():
        for lab,rr in [("all",allrows),("adm",adm)]:
            # skip collinear arch+const for full polynomial? keep and report
            r=report(f"{tag}-{lab}",rr,names)
            if r: r["status"]="LP_OK"; results.append(r)
    json.dump(results,open("coord/decomp_lp_results.json","w"),indent=1)
    print("wrote coord/decomp_lp_results.json",flush=True)
