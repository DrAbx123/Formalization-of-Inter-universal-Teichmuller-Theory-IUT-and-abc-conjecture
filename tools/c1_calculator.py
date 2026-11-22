#!/usr/bin/env python3
"""C1 local-term calculator (route C1). MODEL calculator, not a proof.

A917 correction: semistable multiplicative bad p not in {2,3,ell} => e=1, H=0.
p=2,3: Sage local_data measured reduction type/conductor exponent; wild e estimated
as p^(conductor_exp) (MODEL for H). Infinity: arch=log(sqrt2*pi) C0 placeholder.
Ind2: C0 tentative formula.
"""
import math, json, os

_SAGE={}
_p=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),'coord','c1_sage_raw.json')
if os.path.exists(_p):
    try:
        for _r in json.load(open(_p,encoding='utf-8')):
            _SAGE[(_r['base'],_r['k'])]=_r
    except Exception:
        _SAGE={}

def factor(n):
    n=abs(n); out={}
    d=2
    while d*d<=n:
        while n%d==0:
            out[d]=out.get(d,0)+1; n//=d
        d += 1 if d==2 else 2
    if n>1: out[n]=out.get(n,0)+1
    return out

def is_prime(n):
    if n<2: return False
    if n%2==0: return n==2
    d=3
    while d*d<=n:
        if n%d==0: return False
        d+=2
    return True

def vp(n,p):
    n=abs(n); k=0
    while n%p==0 and n!=0:
        n//=p; k+=1
    return k

def arch_defect(N):
    # paper-MODEL: log((2^(N-1))!)/2^N
    from math import lgamma, log
    return lgamma(2**(N-1)+1.0)/(2.0**N)

def arch_for_nC(nC):
    # packet of N complex factors; N = i+2 for capsule i (lana LocalEstimate:334)
    return sum(arch_defect(i+2) for i in range(nC))/nC

def invariants(A,B):
    Delta=16*B*B*(A*A-4*B)
    c4=16*(A*A-3*B)
    return Delta,c4

def local_terms(A,B,ell,nC,arch=None,sage_key=None):
    if arch is None:
        arch=arch_for_nC(nC)
    Delta,c4=invariants(A,B)
    if Delta==0: return None
    l=2*nC+1
    sF=(nC+1)*(2*nC+1)/6.0
    H={}; T={}; Ind={}; kinds={}
    srec=_SAGE.get(sage_key) if sage_key else None
    for p in factor(Delta):
        typ='mult' if c4%p!=0 else 'add'
        measured=None; e=1; wild=False
        if p in (2,3):
            wild=True
            if srec and str(p) in srec.get('local',{}):
                measured=str(srec['local'][str(p)].get('type',''))
                cond=int(srec['local'][str(p)].get('conductor_exp',0) or 0)
                e=max(2, p**max(1,cond))
            else:
                e=p
        elif p==ell:
            wild=True; e=ell
        elif typ=='mult':
            e=1
        else:
            wild=True; e=ell-1
        Hp=(1-1.0/e)*math.log(p)
        is_mult_sage = measured is not None and 'multiplicative' in measured
        is_mult = (typ=='mult') or is_mult_sage
        ordq=vp(Delta,p) if (is_mult and p not in (2,3)) else 0
        Tp=(sF-1)*ordq*math.log(p)/(2*l)
        ind=0.0
        for j in range(1,nC+1):
            x=j*j*ordq/(2*l); ind+=(x-math.floor(x))*math.log(p)
        H[p]=Hp; kinds[p]=(typ,wild,e,measured); T[p]=Tp; Ind[p]=ind
    H[0]=arch; kinds[0]=('inf',False,1,None); T[0]=0.0; Ind[0]=0.0
    V=sum(H.values()); Ts=sum(T.values()); Is=sum(Ind.values())
    return dict(Delta=Delta,c4=c4,kinds=kinds,l=l,sF=sF,H=H,T=T,Ind=Ind,
                V=V,Ttot=Ts,Indtot=Is,M=V+Is-Ts,arch=arch)

def admissible(A,B,ell,nC,sage_key=None):
    if not is_prime(ell) or ell<=3: return False,'ell not prime>3'
    r=local_terms(A,B,ell,nC,sage_key=sage_key)
    if r is None: return False,'singular'
    for p,val in r['kinds'].items():
        if p==0: continue
        typ,wild,e,measured=val
        if p==ell: return False,'ell is bad'
        if p not in (2,3) and typ=='mult':
            if vp(r['Delta'],p)%ell==0: return False,'ell divides ord_v(q)'
    return True,'ok'

def freq(A,B,k):
    a=1; b=B; c=a+b
    return (b-a, -a*b)

if __name__=='__main__':
    for base in [2,3]:
        for k in range(2,12):
            A2,B2=freq(1,base**k-1,k)
            r=local_terms(A2,B2,5,2,sage_key=(base,k))
            print(base,k,abs(r['Delta']),r['V'],r['Ttot'],r['Indtot'],r['M'])