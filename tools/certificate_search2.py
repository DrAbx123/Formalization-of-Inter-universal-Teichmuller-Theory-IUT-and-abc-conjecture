#!/usr/bin/env python3
"""A1039: general certificate search over a large nonnegative inequality library.
Target: c1 e-exact M = arch + H_tame + Ind2 - T (N<=2000 admissible, l=5).
Features: nonnegative local/global terms + AM-GM/Young/Holder/Jensen/telescoping/weights;
IUT anchors j^2/(2l), (l+1)/24, 1/6 are included as fixed features.
Solver: LP min t s.t. |M - sum lambda f| <= t, lambda>=0; then greedy + random restarts.
Pure Python (numpy/scipy)."""
import json,math,csv,collections,random,itertools
import numpy as np
from scipy.optimize import linprog

l=5; ell=5; nC=2; e=2*ell; sF=2.5
terms=collections.defaultdict(list)
for line in open("coord/c1_local_terms_e_exact.jsonl"):
    r=json.loads(line); terms[(r["N"],r["label"])].append(r)

def features_for(rs):
    arch=H=Ind=T=A=Slog=Sv=Svl=0.0
    # per-j and per-prime group
    fraclog=[0.0]*nC; floorlog=[0.0]*nC; qscale_j=[0.0]*nC
    groups=[(2,2),(3,3),(5,5),(7,7),(11,11),(13,13),(17,17),(19,19),(23,50),(51,10**9)]
    gsum=[0.0]*len(groups); gv=[0.0]*len(groups); gfrac=[0.0]*len(groups)
    vlist=[]; loglist=[]; nb=0
    for r in rs:
        p=int(r["p"]); v=int(r["ord_p_q"])
        if p==0: arch+=r["H_p"]; continue
        if p==ell: continue
        logp=math.log(p); H+=r["H_p"]; Ind+=r["Ind2_p"]; T+=r["T_p"]
        Slog+=logp; Sv+=v; Svl+=v*logp; nb+=1
        if p>3: A+=v*logp/(2*l); vlist.append(v); loglist.append(logp)
        for j in range(nC):
            x=(j+1)**2*v/(2*l); fraclog[j]+=(x-math.floor(x))*logp; floorlog[j]+=math.floor(x)*logp
            qscale_j[j]+=((j+1)**2)*v*logp/(2*l)
        for gi,(lo,hi) in enumerate(groups):
            if lo<=p<=hi:
                gsum[gi]+=logp; gv[gi]+=v; gfrac[gi]+= (v*logp/(2*l))
                break
    if not vlist: vlist=[0]; loglist=[0]
    f={}
    f["const"]=1.0; f["arch"]=arch; f["H"]=H; f["Ind"]=Ind; f["T"]=T; f["A"]=A
    f["Slog"]=Slog; f["Sv"]=float(Sv); f["Svl"]=Svl; f["nbad"]=float(nb)
    f["maxv"]=float(max(vlist)); f["minv"]=float(min(vlist)); f["maxlog"]=max(loglist); f["minlog"]=min(loglist)
    for j in range(nC):
        f[f"Ind{j+1}"]=fraclog[j]; f[f"floor{j+1}"]=floorlog[j]; f[f"qscale{j+1}"]=qscale_j[j]
    for gi in range(len(groups)):
        f[f"g{gi}_log"]=gsum[gi]; f[f"g{gi}_vlog"]=gv[gi]; f[f"g{gi}_A"]=gfrac[gi]
    # IUT anchors
    f["anchor_j2"]=sum(qscale_j)/sF if False else sum(qscale_j)  # sum j^2 vlog/(2l)
    f["anchor_l1"]=((l+1)/24.0)*Slog
    f["anchor_16"]=(1.0/6.0)*Slog
    # AM-GM / Holder / Young / Jensen/telescoping / weights (all nonnegative)
    f["amgm_HInd"]=2.0*math.sqrt(max(0.0,H*Ind))
    f["amgm_AT"]=2.0*math.sqrt(max(0.0,A*T))
    f["HInd"]=H*Ind; f["H2div"]=H*H/(1.0+H); f["T2div"]=T*T/(1.0+T)
    f["holder1"]=math.sqrt(sum(x*x for x in fraclog))*math.sqrt(H)
    f["telescope"]=sum(((j+2)**2-(j+1)**2)*fraclog[j] for j in range(nC))
    f["wlog_mean"]=Slog/nb if nb else 0.0
    f["wvlog_mean"]=Svl/nb if nb else 0.0
    f["ratio_Hlog"]=H/(1.0+Slog); f["ratio_Indlog"]=Ind/(1.0+Slog)
    f["one_split"]=sum(1.0/nb for _ in range(nb)) if nb else 0.0
    return f
recs=[]
for k,rs in terms.items():
    if not rs[0]["admissible"]: continue
    f=features_for(rs); f["M"]=f["arch"]+f["H"]+f["Ind"]-f["T"]; recs.append(f)
maxA=max(r["A"] for r in recs); maxT=max(r["T"] for r in recs); maxH=max(r["H"] for r in recs); maxI=max(r["Ind"] for r in recs); maxS=max(r["Slog"] for r in recs)
for r in recs:
    r["C_A"]=maxA+1-r["A"]; r["C_T"]=maxT+1-r["T"]; r["C_H"]=maxH+1-r["H"]; r["C_Ind"]=maxI+1-r["Ind"]; r["C_Slog"]=maxS+1-r["Slog"]
    r["negT"]=-r["T"]; r["negA"]=-r["A"]; r["neg1"]=-1.0; r["negSlog"]=-r["Slog"]
allnames=[k for k in recs[0] if k!="M"]
positive_names=[k for k in allnames if not k.startswith("neg")]
signed_names=allnames
names=positive_names
print("records",len(recs),"features",len(names))
F=np.array([[r[n] for n in names] for r in recs],float); y=np.array([r["M"] for r in recs],float)
def solve(sub):
    X=F[:,[names.index(n) for n in sub]]; n,m=X.shape
    c=np.zeros(m+1);c[-1]=1
    A=np.vstack([np.hstack([X,-np.ones((n,1))]),np.hstack([-X,-np.ones((n,1))])]);b=np.concatenate([y,-y])
    res=linprog(c,A_ub=A,b_ub=b,bounds=[(0,None)]*m+[(0,None)],method="highs")
    if not res.success: return None
    lam=res.x[:m]; resid=X@lam-y; ar=np.abs(resid)
    return dict(t=float(res.fun),lam=[float(x) for x in lam],names=sub,maxr=float(ar.max()),
                cov=float(np.mean(ar<=1e-6)),coef={n:float(lam[i]) for i,n in enumerate(sub) if abs(lam[i])>1e-8})
# univariate ranking
scores=[]
for n in names:
    r=solve([n])
    if r: scores.append((r["t"],n))
scores.sort()
top=[n for t,n in scores[:20]]
print("top univariate",scores[:10])
# full LP
full=solve(names); print("POSITIVE FULL t",full["t"],"cov",full["cov"]); print("positive full coef",full["coef"])
signed=solve(signed_names); print("SIGNED t",signed["t"],"coef",signed["coef"])
# greedy
selected=[]; bestfull=None; cur=solve(["const"]); best_t=cur["t"]
for step in range(15):
    cand=None
    for n in top+names:
        if n in selected: continue
        r=solve(selected+[n])
        if r and (cand is None or r["t"]<cand[0]): cand=(r["t"],n,r)
    if cand is None: break
    selected.append(cand[1]); bestfull=cand[2]
    print("greedy",step+1,cand[1],cand[0])
    if cand[0]<=1e-8: break
# random restarts over top
random.seed(1); best=full
for it in range(15):
    k=random.randint(4,len(top)); sub=random.sample(top,k)
    r=solve(sub)
    if r and r["t"]<best["t"]: best=r; print("restart",it,"k",k,"t",r["t"])
print("BEST t",best["t"],"coef",best["coef"],"cov",best["cov"])
json.dump({"n":len(recs),"features_positive":names,"features_signed":signed_names,"iut_anchors":["j^2/(2ell)","(ell+1)/24","1/6"],
           "positive_full":full,"signed_full":signed,"greedy":{"selected":selected,"result":bestfull},"best":best,
           "top_univariate":scores[:20]},
          open("coord/certificate_search_results.json","w"),indent=1)
# CSV feature matrix + target
with open("coord/certificate_search_features.csv","w",newline="") as fh:
    fields=["N","label","M"]+names
    w=csv.DictWriter(fh,fieldnames=["N","label","M"]+names);w.writeheader()
    for r in recs: w.writerow({k:r.get(k) for k in ["N","label","M"]+names})
print("wrote results/features")
