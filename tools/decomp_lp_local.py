#!/usr/bin/env python3
"""A1005: LP/Farkas on per-curve C1 local terms.
Input: coord/c1_local_terms.jsonl (MODEL-PAPER), coord/c1_margin_v2.csv.
Features are nonnegative local aggregates (arch, positive net local terms by prime bin).
"""
import json, math, csv, collections
import numpy as np
from scipy.optimize import linprog

BINS=[(2,5),(5,10),(10,20),(20,50),(50,100),(100,200),(200,500),(500,1000),(1000,2000)]
def binidx(p):
    for i,(lo,hi) in enumerate(BINS):
        if lo<=p<hi: return i
    return len(BINS)-1

def load():
    terms=collections.defaultdict(list)
    for line in open('coord/c1_local_terms.jsonl'):
        r=json.loads(line); terms[(r['N'],r['label'])].append(r)
    M={}
    adm={}
    for r in csv.DictReader(open('coord/c1_margin_v2.csv')):
        M[(int(r['N']),r['label'])]=float(r['M']); adm[(int(r['N']),r['label'])]=(r['admissible']=='True')
    out=[]
    for k,rs in terms.items():
        arch=sum(r['arch'] for r in rs)
        H=sum(r['H_p'] for r in rs); Ind=sum(r['Ind2_p'] for r in rs); T=sum(r['T_p'] for r in rs)
        posb=[0.0]*len(BINS); negb=[0.0]*len(BINS)
        for r in rs:
            net=r['H_p']+r['Ind2_p']-r['T_p']
            if net>=0: posb[binidx(int(r['p']))]+=net
            else: negb[binidx(int(r['p']))]+=-net
        posnet=sum(posb); negabs=sum(negb)
        out.append(dict(N=k[0],label=k[1],M=M[k],admissible=adm[k],arch=arch,H=H,Ind=Ind,T=T,
                        posnet=posnet,negabs=negabs,posb=posb,negb=negb))
    return out

def solve(rows,names,getx):
    F=np.array([[getx(r)[n] for n in names] for r in rows],dtype=float)
    y=np.array([r['M'] for r in rows],dtype=float)
    n,m=F.shape
    c=np.zeros(m+1); c[-1]=1.0
    A=np.vstack([np.hstack([F,-np.ones((n,1))]), np.hstack([-F,-np.ones((n,1))])])
    b=np.concatenate([y,-y])
    res=linprog(c,A_ub=A,b_ub=b,bounds=[(0,None)]*m+[(0,None)],method='highs')
    if not res.success: return None
    lam=res.x[:m]; resid=F@lam-y
    marg=res.ineqlin.marginals
    return dict(t=float(res.fun),lam=lam.tolist(),resid=resid.tolist(),
                dual=[float(x) for x in marg],dual_obj=float(np.dot(b,marg)),
                dual_sum=float(sum(marg)),names=names)

def summarize(tag,r,rows):
    resid=np.array(r['resid']); ar=np.abs(resid)
    out=dict(tag=tag,n=len(rows),names=r['names'],t=r['t'],lambda_=r['lam'],
             max_abs=float(ar.max()),mean_abs=float(ar.mean()),rmse=float(np.sqrt((resid**2).mean())),
             **{"cov_1e-6":float(np.mean(ar<=1e-6)),"cov_1e-3":float(np.mean(ar<=1e-3)),"cov_0p01":float(np.mean(ar<=0.01))},
             dual_obj=r['dual_obj'],dual_sum=r['dual_sum'],
             dual_leq0=all(x<=1e-9 for x in r['dual']))
    print(json.dumps(out,indent=1)[:5000])
    return out

def make_getx():
    def g(r):
        d={'const':1.0,'arch':r['arch'],'posnet':r['posnet'],'H':r['H'],'Ind':r['Ind'],'T':r['T'],'negabs':r['negabs']}
        for i in range(len(BINS)): d[f'posbin{i}']=r['posb'][i]
        return d
    return g

if __name__=='__main__':
    rows=load(); g=make_getx()
    print('curves',len(rows),'clean',sum(1 for r in rows if r['negabs']<=1e-12),
          'neg_curves',sum(1 for r in rows if r['negabs']>1e-12),'adm',sum(1 for r in rows if r['admissible']))
    res=[]
    # clean subset: all local net terms nonnegative -> arch + sum posbin should be exact
    clean=[r for r in rows if r['negabs']<=1e-12]
    names_clean=['arch']+[f'posbin{i}' for i in range(len(BINS))]
    r=solve(clean,names_clean,g); res.append(summarize('clean_exact',r,clean))
    # full: nonnegative features incl positive parts, arch, aggregate H/Ind/T
    names_full=['const','arch','posnet','H','Ind','T']+[f'posbin{i}' for i in range(len(BINS))]
    r=solve(rows,names_full,g); res.append(summarize('full',r,rows))
    # admissible subset
    adm=[r for r in rows if r['admissible']]
    r=solve(adm,names_full,g); res.append(summarize('adm',r,adm))
    json.dump(res,open('coord/decomp_lp_local_results.json','w'),indent=1)
    # feature CSV
    with open('coord/c1_local_features.csv','w',newline='') as fh:
        w=csv.writer(fh); w.writerow(['N','label','M','admissible','arch','H','Ind','T','posnet','negabs']+[f'posbin{i}' for i in range(len(BINS))])
        for r in rows: w.writerow([r['N'],r['label'],r['M'],r['admissible'],r['arch'],r['H'],r['Ind'],r['T'],r['posnet'],r['negabs']]+r['posb'])
    print('wrote coord/decomp_lp_local_results.json, coord/c1_local_features.csv',flush=True)
