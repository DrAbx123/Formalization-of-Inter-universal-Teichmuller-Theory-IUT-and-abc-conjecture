import json, math
import numpy as np

rows=[json.loads(l) for l in open('data/c2_invariants.jsonl',encoding='utf-8')]
n=len(rows)
def feats(r):
    N=max(r['N'],2); D=abs(r['discriminant']); d=max(r['modular_degree'],1)
    lN=math.log(N); lD=math.log(D); ld=math.log(d)
    bc=len(r['bad_primes']); mv=max(r['vp_delta'].values()) if r['vp_delta'] else 0
    return lN,lD,ld,bc,mv,d
X=[]; M=[]; names=[]
for r in rows:
    lN,lD,ld,bc,mv,d=feats(r)
    X.append([1.0,lN,lD,bc,mv]); M.append(ld-0.15*lN); names.append(r['label'])
X=np.array(X); M=np.array(M)
# full and holdout regression M0 ~ 1,logN,logD,bad,mv
def ols(X,y):
    coef,res,rank,sv=np.linalg.lstsq(X,y,rcond=None)
    pred=X@coef; resid=y-pred
    ss_res=float(np.sum(resid**2)); ss_tot=float(np.sum((y-y.mean())**2))
    return coef,pred,resid,(1-ss_res/ss_tot if ss_tot else 0)
coef,pred,resid,r2=ols(X,M)
idx=np.arange(n); rng=np.random.default_rng(20261112); rng.shuffle(idx); cut=int(n*0.8)
tr,te=idx[:cut],idx[cut:]
coef_tr,_,_,_=ols(X[tr],M[tr]); pred_te=X[te]@coef_tr; resid_te=M[te]-pred_te
# known-equivalence prediction: logdeg ~ logN + logD/6
K=np.array([0.85*math.log(max(r['N'],2))+math.log(abs(r['discriminant']))/6 for r in rows])
resK=M-K
# relation candidates: empirical quantiles and segment bounds
q=np.quantile(M,[0,0.01,0.5,0.99,1])
# residual vs bad count / maxvp
seg=[]
for bc in sorted(set(int(x[3]) for x in X)):
    mask=np.array([int(x[3])==bc for x in X]); seg.append((bc,int(mask.sum()),float(M[mask].min()),float(M[mask].max()),float(resK[mask].min()),float(resK[mask].max())))
segv=[]
for mv in sorted(set(int(x[4]) for x in X)):
    mask=np.array([int(x[4])==mv for x in X]); segv.append((mv,int(mask.sum()),float(M[mask].min()),float(M[mask].max()),float(resK[mask].min()),float(resK[mask].max())))
out={
 'n':n,
 'M0':{'min':float(M.min()),'max':float(M.max()),'mean':float(M.mean()),'q':[float(x) for x in q]},
 'known_equiv':{'formula':'M0_known=0.85*logN+log|D|/6','res_min':float(resK.min()),'res_max':float(resK.max()),'res_mean':float(resK.mean())},
 'ols_M0':{'coef':[float(x) for x in coef],'r2':r2,'resid_min':float(resid.min()),'resid_max':float(resid.max()),'test_r2':float(1-np.sum(resid_te**2)/np.sum((M[te]-M[te].mean())**2)),'test_resid_min':float(resid_te.min()),'test_resid_max':float(resid_te.max())},
 'byspiro':{'logD_over_logN':{'min':float(min(math.log(abs(r['discriminant']))/math.log(max(r['N'],2)) for r in rows)),'max':float(max(math.log(abs(r['discriminant']))/math.log(max(r['N'],2)) for r in rows))}},
 'seg_badcount':seg,'seg_maxvp':segv,
}
print(json.dumps(out,indent=1))
