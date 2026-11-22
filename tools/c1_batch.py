import json, math, csv, sys
def arch_defect(N):
    return math.lgamma(2**(N-1)+1.0)/(2.0**N)
def arch_for_nC(nC):
    return sum(arch_defect(i+2) for i in range(nC))/nC
ell=5; nC=2; l=5; sF=(nC+1)*(2*nC+1)/6.0
arch=arch_for_nC(nC)
H2=(1-1.0/2)*math.log(2)
H3=(1-1.0/3)*math.log(3)
def margin(rec):
    bad=[int(p) for p in rec.get('bad_primes',[])]
    vpd={int(k):int(v) for k,v in rec.get('vp_delta',{}).items()}
    adm=True
    H=arch; T=0.0; Ind=0.0
    for p in bad:
        if p==ell: adm=False; continue
        if p==2:
            H+=H2; continue
        if p==3:
            H+=H3; continue
        # semistable odd multiplicative p (bad list); e=1 => H=0
        vp=vpd.get(p,0)
        if vp%ell==0: adm=False
        T+=(sF-1)*vp*math.log(p)/(2*l)
        for j in range(1,nC+1):
            x=j*j*vp/(2*l); Ind+=(x-math.floor(x))*math.log(p)
    return H+Ind-T, adm
inp=r'D:\lean\data\c2_invariants.jsonl'; outp=r'D:\lean\coord\c1_margin_v2.csv'
rows=[]; neg=0; adm=0
with open(inp,encoding='utf-8') as f, open(outp,'w',newline='',encoding='utf-8') as g:
    w=csv.writer(g); w.writerow(['N','label','nbad','M','admissible'])
    for line in f:
        rec=json.loads(line)
        M,ok=margin(rec)
        rows.append((rec['N'],rec['label'],len(rec.get('bad_primes',[])),M,ok))
        if M<0: neg+=1
        if ok: adm+=1
        w.writerow([rec['N'],rec['label'],len(rec.get('bad_primes',[])),f"{M:.6f}",ok])
print('total',len(rows),'admissible',adm,'negative',neg)
Ms=sorted(r[3] for r in rows)
print('min',Ms[0],'max',Ms[-1])
for q in [0.01,0.05,0.25,0.5,0.75,0.95,0.99]:
    print('q',q,Ms[int(q*(len(Ms)-1))])
print('negative samples:')
for r in [r for r in rows if r[3]<0][:10]:
    print(r)
