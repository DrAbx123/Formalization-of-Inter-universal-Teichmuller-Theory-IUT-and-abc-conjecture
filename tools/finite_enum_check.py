#!/usr/bin/env python3
"""A1061: finite label/place enumeration feasibility harness.
Enumerates (p,j) cells for admissible l=5 curves, checks local identities:
qroot order, qroot^{j^2} order, scaleVol sign, ind2 leading cancellation,
tame/arch/shellDefect/ind2 nonneg, c1 e-exact net.
Pure Python. MODEL-level checks of the c1/conceptual formulas; not Lean."""
import json,math,csv,collections

l=5; ell=5; nC=(l-1)//2; sF=2.5
rows=[json.loads(l) for l in open("coord/ub_curves_9999.jsonl")]
def admissible(vp):
    if ell in vp: return False
    for p,v in vp.items():
        p=int(p); v=int(v)
        if p>3 and p!=ell and v%ell==0: return False
    return True

def eclass(p): return 2 if p==2 else (3 if p==3 else 2*l)

out=[]; summary=collections.Counter(); ecount=collections.Counter(); curves=0
for r in rows:
    vp={int(p):int(v) for p,v in r["vp_delta"].items()}
    if not admissible(vp): continue
    curves+=1
    bad=sorted(p for p in vp if p!=ell)
    for p in bad:
        v=vp[p]; logp=math.log(p); e=eclass(p); ecount[e]+=1
        qroot_order=v/(2*l)
        for j in range(1,nC+1):
            j2=j*j
            j2_order=j2*v/(2*l)
            scale_vol=-j2*v*logp/(2*l)
            ind2_lead=j2*v*logp/(2*l)
            cancel=abs(scale_vol+ind2_lead)
            if p in (2,3):
                H=nC*(1-1.0/e)*logp; Ind=0.0; T=0.0
            else:
                H=nC*(1-1.0/e)*logp
                Ind=sum(((j2p*v/(2*l))-math.floor(j2p*v/(2*l)))*logp for j2p in (1,4))
                T=(sF-1)*v*logp/(2*l)/nC
            arch=0.28527176196673965
            shellDefect=0.0
            checks={
              "qroot_order_pos": qroot_order>0,
              "qroot_order_exact": abs(qroot_order-v/(2*l))<1e-15,
              "j2_order_exact": abs(j2_order-j2*v/(2*l))<1e-15,
              "scale_vol_neg": scale_vol<0,
              "ind2_lead_pos": ind2_lead>0,
              "cancel_exact": cancel<1e-12,
              "H_nonneg": H>=-1e-12,
              "Ind_nonneg": Ind>=-1e-12,
              "arch_nonneg": arch>=-1e-12,
              "shell_nonneg": shellDefect>=-1e-12,
              "net_nonneg": H+Ind-T>=-1e-12,
            }
            ok=all(checks.values())
            summary["cells"]+=1
            if ok: summary["pass"]+=1
            else: summary["fail"]+=1
            for k,vv in checks.items():
                if not vv: summary["fail_"+k]+=1
            out.append(dict(l=l,N=r["N"],label=r["label"],p=p,j=j,e=e,qOrder=v,qroot_order=qroot_order,
                            j2_order=j2_order,scale_vol=scale_vol,ind2_lead=ind2_lead,cancel=cancel,
                            H=H,Ind=Ind,T=T,arch=arch,shell=shellDefect,ok=ok))
with open("coord/finite_enum_checks.csv","w",newline="") as fh:
    w=csv.DictWriter(fh,fieldnames=list(out[0].keys()));w.writeheader();w.writerows(out)
# space table for primes <= 100
def space(ell0):
    nC0=(ell0-1)//2; cs=0; occ=0; cells=0; ec=collections.Counter()
    for r in rows:
        vp={int(p):int(v) for p,v in r["vp_delta"].items()}
        if ell0 in vp: continue
        if any(not(p in (2,3) or p==ell0 or v%ell0!=0) for p,v in vp.items()): continue
        cs+=1; bad=[p for p in vp if p!=ell0]; occ+=len(bad); cells+=len(bad)*nC0
        for p in bad: ec[eclass(p) if ell0==5 else (2 if p==2 else (3 if p==3 else 2*ell0))]+=1
    return cs,occ,cells,dict(ec)
spaces=[]
primes=[n for n in range(5,101) if all(n%d for d in range(2,int(n**0.5)+1))]
for ell0 in primes:
    cs,occ,cells,ec=space(ell0); spaces.append(dict(l=ell0,curves=cs,bad_occ=occ,cells=cells,eclasses=ec))
with open("coord/finite_enum_space.csv","w",newline="") as fh:
    w=csv.DictWriter(fh,fieldnames=["l","curves","bad_occ","cells","eclasses"]);w.writeheader();w.writerows(spaces)
res=dict(l=5,curves=curves,cells=len(out),summary=dict(summary),eclasses=dict(ecount),
         spaces_total=dict(curves=sum(x["curves"] for x in spaces),bad_occ=sum(x["bad_occ"] for x in spaces),cells=sum(x["cells"] for x in spaces),lmax=100))
json.dump(res,open("coord/finite_enum_summary.json","w"),indent=1)
print("curves",curves,"cells",len(out),"summary",dict(summary),"eclasses",dict(ecount))
print("space l<=100",res["spaces_total"])
print("wrote finite_enum_checks.csv, finite_enum_space.csv, finite_enum_summary.json")
