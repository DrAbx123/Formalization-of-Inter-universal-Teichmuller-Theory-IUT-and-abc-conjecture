"""Exact finite checks for the source-symplectic span argument.

The Galois realization is supplied by Kondo v2 Lemma 3.3 and the source
procession construction, not proved by these linear-algebra computations.
The basis changes below test the basis-independent lattice lemma; they are
not asserted to be arbitrary permitted source automorphisms.
"""
from fractions import Fraction as F
from math import gcd
from pathlib import Path
import json
from sympy import isprime


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def inverse_mod(a, p):
    n = len(a)
    aug = [row[:] + identity(n)[i] for i, row in enumerate(a)]
    for j in range(n):
        k = next(k for k in range(j, n) if aug[k][j] % p)
        aug[k], aug[j] = aug[j], aug[k]
        u = pow(aug[j][j] % p, -1, p)
        aug[j] = [(u*x) % p for x in aug[j]]
        for i in range(n):
            if i != j:
                c = aug[i][j]
                aug[i] = [(x-c*y) % p for x,y in zip(aug[i],aug[j])]
    assert [row[:n] for row in aug] == identity(n)
    return [row[n:] for row in aug]


def add_basis(rows, v, p):
    v = [x % p for x in v]
    for pivot,w in rows:
        c = v[pivot]
        if c:
            v = [(x-c*y) % p for x,y in zip(v,w)]
    try:
        pivot = next(i for i,x in enumerate(v) if x)
    except StopIteration:
        return False
    u = pow(v[pivot],-1,p)
    v = [(u*x) % p for x in v]
    # Keep reduced rows ordered by pivot for future elimination.
    for k,(q,w) in enumerate(rows):
        c = w[pivot]
        if c:
            rows[k] = (q,[(x-c*y) % p for x,y in zip(w,v)])
    rows.append((pivot,v))
    rows.sort(key=lambda pair:pair[0])
    return True


def sp_generators(g):
    # Upper/lower unipotents with symmetric elementary blocks.
    return [(side,i,j) for side in (0,1) for i in range(g) for j in range(i,g)]


def act(v, generator, p):
    side,i,j = generator
    g = (len(v)-1)//2
    w = v[:]
    if side == 0:
        w[1+i] = (w[1+i] + v[1+g+j]) % p
        if i != j:
            w[1+j] = (w[1+j] + v[1+g+i]) % p
    else:
        w[1+g+i] = (w[1+g+i] + v[1+j]) % p
        if i != j:
            w[1+g+j] = (w[1+g+j] + v[1+i]) % p
    return w


def alternating(x,y,p):
    g = (len(x)-1)//2
    return sum(x[1+i]*y[1+g+i]-x[1+g+i]*y[1+i] for i in range(g)) % p


def transvection(x,v,c,p):
    a=c*alternating(x,v,p)%p
    return [(q+a*r)%p for q,r in zip(x,v)]


def primitive_transport(x,y,p):
    """At most two finite symplectic transvections send nonzero x to y."""
    assert x[0]==y[0]==0 and any(x) and any(y)
    if x==y:
        return []
    xy=alternating(x,y,p)
    if xy:
        v=[(b-a)%p for a,b in zip(x,y)]
        c=pow(xy,-1,p)
        assert transvection(x,v,c,p)==y
        return [(v,c)]
    basis=identity(len(x))[1:]
    z=next((v for v in basis if alternating(x,v,p) and alternating(v,y,p)),None)
    if z is None:
        u=next(v for v in basis if alternating(x,v,p))
        v=next(v for v in basis if alternating(v,y,p))
        z=[(a+b)%p for a,b in zip(u,v)]
    assert alternating(x,z,p) and alternating(z,y,p)
    return primitive_transport(x,z,p)+primitive_transport(z,y,p)


def source_span_case(e,p,t,seed):
    assert isprime(e) and isprime(p) and p>e+1 and (p-1)%e==0
    assert 1<=t<e
    # J=m_K has basis (p,pi,...,pi^(e-1)). Trace is its first coordinate,
    # up to the common nonzero factor e*p. Change this basis arbitrarily
    # within the stated trace-adapted integral class.
    b = identity(e)
    for k in range(1,2*e+1):
        i = 1+(k+seed)%(e-1)
        j = (3*k+seed)%e
        if i==j:
            j=0
        c = 1+(k*seed+2*k)%7
        b[i] = [(x+c*y)%p for x,y in zip(b[i],b[j])]
    assert b[0] == identity(e)[0]
    inv = inverse_mod(b,p)
    # Direct field-hull witness: pi^t and pi are both primitive in ker Tr.
    source=[inv[i][t] for i in range(e)]
    target=[inv[i][1] for i in range(e)]
    moves=primitive_transport(source,target,p)
    out=source[:]
    for v,c in moves:
        out=transvection(out,v,c,p)
    assert out==target
    physical=[sum(b[i][j]*out[j] for j in range(e))%p for i in range(e)]
    assert physical==identity(e)[1]
    # A_t=pi^t O_K contains pJ; modulo pJ it has first coordinate and
    # coordinates t,...,e-1, with codimension t-1 in J.
    rows=[]
    for j in [0,*range(t,e)]:
        add_basis(rows,[inv[i][j] for i in range(e)],p)
    initial_rank=len(rows)
    assert initial_rank==e-t+1
    generators=sp_generators((e-1)//2)
    rounds=0
    while len(rows)<e:
        rounds+=1
        old=len(rows)
        previous=[v[:] for _,v in rows]
        for gen in generators:
            for v in previous:
                add_basis(rows,act(v,gen,p),p)
                if len(rows)==e:
                    break
            if len(rows)==e:
                break
        assert len(rows)>old
        assert rounds<=e
    return {'e':e,'p':p,'t':t,'basis_change_seed':seed,
            'initial_residue_rank':initial_rank,'final_residue_rank':len(rows),
            'closure_rounds':rounds,'quotient_length_J_over_A':t-1,
            'normalized_hull_gain_per_log_p':str(F(t-1,e)),
            'direct_uniformizer_residue_witness':{
                'source_pi_power':t,'target_pi_power':1,
                'finite_transvection_count':len(moves),
                'target_nonzero_in_m_over_m_squared':True,
                'precision':'mod p*m_K, which is contained in m_K^2',
                'transvections':[{'vector':v,'coefficient':c} for v,c in moves]}}


def layer(e,j,b,rho,source_sp):
    r=j+1
    s,t=divmod(b*j*j,e)
    assert t
    delta=F(e-1,2*e)*(r*rho-1+(1-rho)**r)
    frac=F(1,e)**r if source_sp else F(t,e)**r
    return -delta-rho**r*(s+frac)


def procession(e,b,rho,source_sp,deep=False):
    m=(e-1)//2
    v=sum((layer(e,j,b,rho,source_sp) for j in range(1,m+1)),F(0))/m
    return v-F(m+3,2) if deep else v


def aligned_hull(e,b,rho,deep=False):
    """Target hull after the actual complete-Ind1 field-copy alignment.

    This formula is justified by the natural-language source argument,
    not by treating a general additive transport as a ring map.
    """
    m=(e-1)//2
    val=F(0)
    for j in range(1,m+1):
        s,t=divmod(b*j*j,e)
        assert t
        val-=rho**(j+1)*(s+F(1,e))/m
    return val-F(m+3,2) if deep else val


def aligned_thresholds(e,deep):
    m=(e-1)//2
    rho=F(1,2)
    slope=sum((j*j*rho**(j+1) for j in range(1,m+1)),F(0))/m
    gain=rho-slope
    assert gain>0
    cases=[]
    for b0 in range(1,e):
        gap=aligned_hull(e,b0,rho,deep)+rho*F(b0,e)
        k=max(0,ceil_fraction(-gap/gain))
        while (b0+e*k)%3:
            k+=1
        b=b0+e*k
        v=aligned_hull(e,b,rho,deep)
        q=-rho*F(b,e)
        assert v>=q
        assert aligned_hull(e,b+e,rho,deep)==v-slope
        if k>=3:
            assert aligned_hull(e,b-3*e,rho,deep)<-rho*F(b-3*e,e)
        cases.append({'b_mod_e':b0,'first_admissible_b':b,'gap':str(v-q)})
    first=min(c['first_admissible_b'] for c in cases)
    # Compute the last admissible failing b; after the residue thresholds
    # there can be no later failure by the proved positive affine slope.
    bound=max(c['first_admissible_b'] for c in cases)
    failures=[b for b in range(3,bound+1,3) if b%e and
              aligned_hull(e,b,rho,deep)<-rho*F(b,e)]
    return {'e':e,'deep_unit_domain':deep,'first_b':first,
            'all_admissible_success_from':max(failures,default=0)+3,
            'last_admissible_failure':max(failures,default=None),
            'span_at_first':str(aligned_hull(e,first,rho,deep)),
            'span_at_first_decimal':float(aligned_hull(e,first,rho,deep)),
            'native_at_first':str(-rho*F(first,e)),
            'residue_cases':cases}


def ceil_fraction(x):
    return -((-x.numerator)//x.denominator)


def thresholds(e,deep):
    m=(e-1)//2
    rho=F(1,2)
    slope=sum((j*j*rho**(j+1) for j in range(1,m+1)),F(0))/m
    gain=rho-slope
    assert gain>0
    cases=[]
    for b0 in range(1,e):
        gap=procession(e,b0,rho,True,deep)+rho*F(b0,e)
        k=max(0,ceil_fraction(-gap/gain))
        while (b0+e*k)%3:
            k+=1
        b=b0+e*k
        v=procession(e,b,rho,True,deep)
        q=-rho*F(b,e)
        old=procession(e,b,rho,False,deep)
        assert v>=q and v>=old
        assert procession(e,b+e,rho,True,deep)==v-slope
        if k>=3:
            assert procession(e,b-3*e,rho,True,deep)<-rho*F(b-3*e,e)
        cases.append({'b_mod_e':b0,'first_admissible_b':b,'gap':str(v-q),
                      'gain_over_permutation_span':str(v-old)})
    first=min(c['first_admissible_b'] for c in cases)
    return {'e':e,'deep_unit_domain':deep,'first_b':first,
            'sufficient_cutoff':max(c['first_admissible_b'] for c in cases),
            'span_at_first':str(procession(e,first,rho,True,deep)),
            'span_at_first_decimal':float(procession(e,first,rho,True,deep)),
            'native_at_first':str(-rho*F(first,e)),'residue_cases':cases}


def main():
    # Check that the generators preserve the actual alternating form.
    for e,p in ((5,61),(7,43),(11,331),(41,12301)):
        for gen in sp_generators((e-1)//2):
            x=[(3*i+2)%p for i in range(e)]
            y=[(i*i+7)%p for i in range(e)]
            assert alternating(act(x,gen,p),act(y,gen,p),p)==alternating(x,y,p)
    cases=[]
    for e,p in ((5,61),(7,43),(11,331)):
        for t in range(1,e):
            for seed in (0,1,9):
                cases.append(source_span_case(e,p,t,seed))
    for t in (1,2,20,40):
        for seed in (0,1,9):
            cases.append(source_span_case(41,12301,t,seed))
    cuts=[thresholds(e,deep) for e in (5,7,11,13,17,19,23,29,31,37,41,43)
          for deep in (False,True)]
    aligned_cuts=[aligned_thresholds(e,deep)
                  for e in (5,7,11,13,17,19,23,29,31,37,41,43)
                  for deep in (False,True)]
    ell41=[]
    for b in (3,273,1620):
        for rho in (F(1,2),F(1)):
            old=procession(41,b,rho,False)
            new=procession(41,b,rho,True)
            aligned=aligned_hull(41,b,rho)
            q=-rho*F(b,41)
            assert aligned>=new>=old
            ell41.append({'b':b,'rho':str(rho),'old':str(old),'new':str(new),
                          'new_decimal':float(new),'q':str(q),
                          'gain':str(new-old),'gap':str(new-q),
                          'aligned_hull':str(aligned),
                          'aligned_hull_decimal':float(aligned),
                          'aligned_hull_gap':str(aligned-q)})
    assert isprime(12301) and (12301-1)%(60*41)==0 and gcd(3240,41)==1
    assert 2694%6==0 and gcd(2694,41)==1 and 2694==2*1347
    result={'task':'C9-TAME-LOG-DOMAIN-20261025','all_assertions_passed':True,
            'finite_symplectic_span_cases':cases,'thresholds':cuts,'ell41':ell41,
            'aligned_hull_thresholds':aligned_cuts,
            'totals':{'finite_span_cases':len(cases),'threshold_cases':len(cuts),
                      'direct_output_point_cases':len(cases),
                      'aligned_hull_threshold_cases':len(aligned_cuts)},
            'local_realization_refinement':{'p':12301,'ell':41,'q_exponent':3240,
                  'mu_60ell_in_Qp':True,'qhat_pi_exponent':1620,
                  'smaller_q_exponent':2694,'smaller_qhat_pi_exponent':1347,
                  'smaller_q_has_rational_6_torsion':True},
            'scope':{'galois_realization':'Kondo v2 Lemma3.3 and source Ind1 construction, not established by matrix tests',
                     'basis_independent_lattice_proof':'natural-language proof in record',
                     'complete_global_source_datum_constructed':False,
                     'original_P6_proved':False,'target_accepted':False}}
    out=Path(__file__).with_name('C9-SOURCE-SYMPLECTIC-SPAN-CERTIFICATE-20261025.json')
    out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'all_assertions_passed':True,'totals':result['totals'],
       'ell41_thresholds':[{k:v for k,v in c.items() if k!='residue_cases'} for c in cuts if c['e']==41],
       'ell41_aligned_thresholds':[{k:v for k,v in c.items() if k!='residue_cases'} for c in aligned_cuts if c['e']==41],
       'ell41':ell41,'target_accepted':False}))


if __name__=='__main__':
    main()
