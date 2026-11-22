#!/usr/bin/env python3
"""A1007: recompute C1 local terms with exact Kummer ramification e=2*ell.
Source: coord/c1_local_terms.jsonl (current model fields), formulas as in c1_batch.
Normalization: H = nC * (1-1/e) log p (sum over j=1..nC), Ind as before,
T = (sF-1) vp logp/(2 l) / nC (1/nC normalization; see report).
model='MODEL-E-EXACT'.
"""
import json, math, csv, collections
nC=2; l=5; ell=5; sF=2.5; e0=2*ell

def frac(x): return x-math.floor(x)

rows=[json.loads(l) for l in open("coord/c1_local_terms.jsonl")]
out=[]
for r in rows:
    p=int(r["p"]); vp=int(r["ord_p_q"]); adm=bool(r["admissible"])
    H=r["H_p"]; Ind=r["Ind2_p"]; T=r["T_p"]; note=""
    if p==0:
        H=r["H_p"]; Ind=0.0; T=0.0; note="arch (MODEL C0)"
    elif p==ell:
        H=Ind=T=0.0; note="p=ell excluded"
    elif p in (2,3):
        H=r["H_p"]*nC; Ind=0.0; T=0.0; note="wild p=2,3: current H model * nC (special)"
    else:
        if vp % ell == 0:
            e=e0//math.gcd(e0,vp); note=f"special ell|ord: e=2ell/gcd={e}"
        else:
            e=e0; note="exact Kummer e=2ell"
        H=nC*(1-1.0/e)*math.log(p)
        Ind=sum(frac(j*j*vp/(2*l))*math.log(p) for j in range(1,nC+1))
        T=(sF-1)*vp*math.log(p)/(2*l)/nC
    net=H+Ind-T
    out.append(dict(N=r["N"],label=r["label"],p=p,ord_p_q=vp,H_p=H,Ind2_p=Ind,T_p=T,
                    arch=H if p==0 else 0.0,admissible=adm,net=net,model='MODEL-E-EXACT',note=note))
with open("coord/c1_local_terms_e_exact.jsonl","w") as fh:
    for r in out: fh.write(json.dumps(r,separators=(",",":"))+"\n")
cols=["N","label","p","ord_p_q","H_p","Ind2_p","T_p","arch","admissible","net","model","note"]
with open("coord/c1_local_terms_e_exact.csv","w",newline="") as fh:
    w=csv.DictWriter(fh,fieldnames=cols); w.writeheader(); w.writerows(out)
curves=collections.defaultdict(list)
for r in out: curves[(r["N"],r["label"])].append(r)
for tag,sel in [("all",lambda k:True),("adm",lambda k:curves[k][0]["admissible"])]:
    neg=[]
    for k,rs in curves.items():
        if not sel(k): continue
        for r in rs:
            if r["net"]<-1e-12: neg.append((r["net"],k,r))
    print(tag,"neg_terms",len(neg),"neg_curves",len(set(k for _,k,_ in neg)),
          "sum",round(sum(x[0] for x in neg),3),"pdist",collections.Counter(r["p"] for _,_,r in neg).most_common(10))
    if tag=="adm":
        for net,k,r in neg[:10]: print(" admneg",k,"p",r["p"],"v",r["ord_p_q"],"net",round(net,4))
# check per-curve M
Ms={}
for k,rs in curves.items(): Ms[k]=sum(r["H_p"]+r["Ind2_p"]-r["T_p"] for r in rs)
print("M range",min(Ms.values()),max(Ms.values()))
print("wrote coord/c1_local_terms_e_exact.jsonl/.csv",len(out))
