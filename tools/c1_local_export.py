#!/usr/bin/env python3
"""A1005: export per-curve per-place C1 local terms (MODEL-PAPER).
Reads data/c2_invariants.jsonl + coord/c1_margin_v2.csv (admissible flag),
writes coord/c1_local_terms.jsonl.
"""
import json, math, csv, sys
sys.path.insert(0,'tools')
from c1_calculator import arch_for_nC

ell=5; nC=2; l=5
sF=(nC+1)*(2*nC+1)/6.0
ARCH=arch_for_nC(nC)

def curve_rows(rec, admissible):
    N=int(rec['N']); lab=rec['label']
    bad=[int(p) for p in rec.get('bad_primes',[])]
    vpd={int(k):int(v) for k,v in rec.get('vp_delta',{}).items()}
    rows=[]
    # arch as p=0
    rows.append(dict(N=N,label=lab,p=0,ord_p_q=0,H_p=ARCH,Ind2_p=0.0,T_p=0.0,arch=ARCH,
                     admissible=admissible,model='MODEL-PAPER',note='arch global (C0 placeholder)'))
    for p in bad:
        if p==ell:
            rows.append(dict(N=N,label=lab,p=p,ord_p_q=vpd.get(p,0),H_p=0.0,Ind2_p=0.0,T_p=0.0,arch=0.0,
                             admissible=False,model='MODEL-PAPER',note='p=ell excluded (admissible false)'))
            continue
        if p==2:
            Hp=(1-1.0/2)*math.log(2); rows.append(dict(N=N,label=lab,p=p,ord_p_q=0,H_p=Hp,Ind2_p=0.0,T_p=0.0,arch=0.0,
                             admissible=admissible,model='MODEL-PAPER',note='p=2 wild model; T/Ind set 0'))
            continue
        if p==3:
            Hp=(1-1.0/3)*math.log(3); rows.append(dict(N=N,label=lab,p=p,ord_p_q=0,H_p=Hp,Ind2_p=0.0,T_p=0.0,arch=0.0,
                             admissible=admissible,model='MODEL-PAPER',note='p=3 wild model; T/Ind set 0'))
            continue
        vp=vpd.get(p,0); logp=math.log(p)
        Hp=0.0                                  # semistable e=1
        Tp=(sF-1)*vp*logp/(2*l)
        Ind=sum((j*j*vp/(2*l)-math.floor(j*j*vp/(2*l)))*logp for j in range(1,nC+1))
        rows.append(dict(N=N,label=lab,p=p,ord_p_q=vp,H_p=Hp,Ind2_p=Ind,T_p=Tp,arch=0.0,
                         admissible=admissible,model='MODEL-PAPER',note='odd semistable multiplicative; e=1 H=0'))
    return rows

def main():
    adm={}
    for r in csv.DictReader(open('coord/c1_margin_v2.csv')):
        adm[(int(r['N']),r['label'])] = (r['admissible']=='True', float(r['M']))
    out=[]; mism=0
    for line in open('data/c2_invariants.jsonl'):
        rec=json.loads(line)
        key=(int(rec['N']),rec['label'])
        ok,Mcsv=adm.get(key,(False,None))
        rows=curve_rows(rec,ok)
        M=sum(r['H_p']+r['Ind2_p']-r['T_p'] for r in rows)
        if Mcsv is not None and abs(M-Mcsv)>2e-6:
            mism+=1
        out.extend(rows)
    with open('coord/c1_local_terms.jsonl','w') as fh:
        for r in out: fh.write(json.dumps(r,separators=(",",":"))+"\n")
    print("rows",len(out),"curves",len({(r['N'],r['label']) for r in out}),"M_mismatch",mism)
    # checks
    Hs={}; Ts={}; Is={}; As={}
    for r in out:
        k=(r['N'],r['label']); Hs[k]=Hs.get(k,0)+r['H_p']; Ts[k]=Ts.get(k,0)+r['T_p']; Is[k]=Is.get(k,0)+r['Ind2_p']; As[k]=As.get(k,0)+r['arch']
    print("sum H+Ind-T range",min(Hs[k]+Is[k]-Ts[k] for k in Hs),max(Hs[k]+Is[k]-Ts[k] for k in Hs))
    print("arch",ARCH)

if __name__=='__main__': main()
