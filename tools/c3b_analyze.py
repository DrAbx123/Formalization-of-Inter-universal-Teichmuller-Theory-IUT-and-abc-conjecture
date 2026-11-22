import csv,json,math
import numpy as np
rows={}
for l in open('data/c2_invariants.jsonl',encoding='utf-8'):
    r=json.loads(l); rows[r['label']]=r
ms=[]
for r in csv.DictReader(open('coord/c1_margin_v2.csv',encoding='utf-8')):
    lab=r['label']; c=rows[lab]; M=float(r['M']); N=int(r['N']); nbad=int(r['nbad']); adm=(r['admissible']=='True')
    D=abs(c['discriminant']); deg=c['modular_degree']; mv=max(c['vp_delta'].values()) if c['vp_delta'] else 0
    ms.append(dict(label=lab,N=N,nbad=nbad,M=M,adm=adm,mv=mv,lN=math.log(max(N,2)),lD=math.log(max(D,2)),ldeg=math.log(max(deg,1)),deg=deg,D=D))
print('n',len(ms))
print('M min/max/mean',min(x['M'] for x in ms),max(x['M'] for x in ms),sum(x['M'] for x in ms)/len(ms))
print('neg',sum(1 for x in ms if x['M']<0),'adm',sum(1 for x in ms if x['adm']))
for key in ['nbad','mv']:
    print('STRAT',key)
    for v in sorted(set(x[key] for x in ms)):
        z=[x for x in ms if x[key]==v]
        if len(z)>0 and (key=='nbad' or len(z)>20):
            print(v,len(z),round(min(x['M'] for x in z),4),round(sum(x['M'] for x in z)/len(z),4),round(max(x['M'] for x in z),4),sum(1 for x in z if x['M']<0))
print('lowest',sorted([(x['M'],x['label'],x['nbad'],x['mv']) for x in ms])[:12])
X=np.array([[1,x['lN'],x['lD'],x['nbad'],x['mv']] for x in ms]); y=np.array([x['M'] for x in ms])
coef,_,_,_=np.linalg.lstsq(X,y,rcond=None); resid=y-X@coef
print('coef',coef.tolist()); print('resid',resid.min(),resid.max(),'r2',1-np.sum(resid**2)/np.sum((y-y.mean())**2))
K=np.array([0.85*x['lN']+x['lD']/6 for x in ms]); rk=y-K
print('known resid',rk.min(),rk.max(),rk.mean())
