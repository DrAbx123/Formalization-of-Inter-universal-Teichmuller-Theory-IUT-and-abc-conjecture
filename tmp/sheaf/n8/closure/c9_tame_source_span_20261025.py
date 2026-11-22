"""Exact actual tensor-order spans, with source-relevant tame ramification.

This is a local calculation and a certificate for its formulas.  It does not
construct a complete global IUT datum or prove the original P6 comparison.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, gcd
from pathlib import Path
import json
from sympy import Matrix, eye, isprime
from sympy.matrices.normalforms import hermite_normal_form


def vp(n,p):
    n=abs(int(n))
    assert n
    ans=0
    while n%p==0:
        n//=p
        ans+=1
    return ans


def matrix_case(e,r,n,p,unit):
    # D=Z_p[x_1,...,x_r]/(x_i^e-p*unit), with its true monomial basis.
    basis=list(product(range(e),repeat=r))
    where={a:i for i,a in enumerate(basis)}
    d=e**r
    columns=[]
    for factor in range(r):
        for a in basis:
            b=list(a)
            exponent=b[factor]+n
            b[factor]=exponent%e
            col=[0]*d
            col[where[tuple(b)]]=(p*unit)**(exponent//e)
            columns.append(col)
    matrix=Matrix(d,len(columns),lambda i,j:columns[j][i])
    # An integral basis change, not an extra source operation.
    change=eye(d)
    for k in range(min(7,d-1)):
        change[k,k+1]=k+1
    assert change.det()==1
    hnf=hermite_normal_form(change*matrix)
    actual=vp(hnf.det(),p)
    single_hnf=hermite_normal_form(change*matrix[:, :d])
    single_length=vp(single_hnf.det(),p)
    q,t=divmod(n,e)
    expected=q*e**r+t**r
    assert actual==expected
    assert single_length==n*e**(r-1)
    quotient_length=single_length-actual
    assert quotient_length==t*e**(r-1)-t**r
    assert (quotient_length>0)==(r>1 and 0<t<e)
    order_length=(r-1)*(e-1)*e**(r-1)//2
    assert 2*order_length==(r-1)*(e-1)*e**(r-1)
    log_span=-F(order_length+actual,e**r)
    log_hull=-F(n,e)
    assert log_span<=log_hull
    return {'e':e,'r':r,'n':n,'p':p,'unit':unit,'rank':d,
            'columns':len(columns),'index_length_relative_to_tensor_order':actual,
            'single_branch_index_length_relative_to_tensor_order':single_length,
            'noncancellable_quotient_length_under_common_additive_transport':quotient_length,
            'tensor_order_index_length_in_integral_closure':order_length,
            'log_span_per_log_p':str(log_span),'log_hull_per_log_p':str(log_hull)}


def layer(e,j,b,rho):
    r=j+1
    c=F(e-1,2*e)
    q,t=divmod(b*j*j,e)
    expected_order_loss=c*(r*rho-1+(1-rho)**r)
    value=-expected_order_loss-rho**r*(q+F(t,e)**r)
    ideal=-rho**r*F(b*j*j,e)
    assert value<=ideal
    return value


def layer_by_tuples(e,j,b,rho):
    r=j+1
    c=F(e-1,2*e)
    q,t=divmod(b*j*j,e)
    total=F(0)
    for tup in product((0,1),repeat=r):
        k=sum(tup)
        prob=rho**k*(1-rho)**(r-k)
        order_loss=c*max(k-1,0)
        extra=(q+F(t,e)**r) if k==r else 0
        total-=prob*(order_loss+extra)
    return total


def procession(e,b,rho,deep_units=False):
    m=(e-1)//2
    value=sum((layer(e,j,b,rho) for j in range(1,m+1)),F(0))/m
    if deep_units:
        # log(exp(p z))=p z on an actual small-unit domain, one factor each.
        value-=F(m+3,2)
    return value


def ceil_fraction(q):
    return -((-q.numerator)//q.denominator)


def thresholds(e,deep_units=False):
    m=(e-1)//2
    rho=F(1,2)
    slope=sum((j*j*rho**(j+1) for j in range(1,m+1)),F(0))/m
    improvement=rho-slope
    assert improvement>0
    residue_cases=[]
    for b0 in range(1,e):
        gap0=procession(e,b0,rho,deep_units)+rho*F(b0,e)
        k=max(0,ceil_fraction(-gap0/improvement))
        while (b0+e*k)%3:
            k+=1
        b=b0+e*k
        value=procession(e,b,rho,deep_units)
        native=-rho*F(b,e)
        assert value>=native
        # Check the proven affine law at a much larger parameter.
        assert procession(e,b+1000*e,rho,deep_units)==value-1000*slope
        if k>=3:
            old=b-3*e
            assert procession(e,old,rho,deep_units)<-rho*F(old,e)
        assert b%3==0 and gcd(b,e)==1
        residue_cases.append({'b_mod_e':b0,'first_b_divisible_by_3':b,
                              'volume_gap_per_log_p':str(value-native)})
    first=min(x['first_b_divisible_by_3'] for x in residue_cases)
    cutoff=max(x['first_b_divisible_by_3'] for x in residue_cases)
    return {'e':e,'m':m,'deep_unit_domain':deep_units,
            'all_bad_largest_block_rank':e**(m+1),
            'first_successful_b':first,'sufficient_cutoff_for_all_admissible_b':cutoff,
            'native_at_first':str(-rho*F(first,e)),
            'span_at_first':str(procession(e,first,rho,deep_units)),
            'span_at_first_decimal':float(procession(e,first,rho,deep_units)),
            'gain_per_b_period_e':str(improvement),'residue_cases':residue_cases}


def main():
    p,e,b=1231,41,1620
    assert isprime(p) and (p-1)%(30*e)==0
    assert (2*b)%30==0 and gcd(2*b,e)==1
    local_tate={'p':p,'ell':e,'b':b,'q_p_exponent':2*b,
                'q_root_30_p_exponent':(2*b)//30,
                'qhat_pi_exponent':b,
                'q_order_coprime_ell':True,
                'mu_30ell_in_Qp':True,
                'rational_30_torsion':'by the stated Tate uniformization argument',
                'complete_global_initial_theta_datum':False}
    cases=[]
    for e,p in ((5,61),(7,337)):
        for n in range(2*e+2):
            cases.append(matrix_case(e,2,n,p,1+(n%2)))
    for n in (1,3,5,9):
        cases.append(matrix_case(5,3,n,61,2))
    checks=0
    for e in (5,7,11):
        for j in range(1,7):
            for b in (3,6,15,42):
                for rho in (F(1,3),F(1,2),F(2,3),F(1)):
                    assert layer(e,j,b,rho)==layer_by_tuples(e,j,b,rho)
                    checks+=1
        m=(e-1)//2
        for b in (3,6,15,42):
            native=-F(b,e)
            ideal=-F(e*(e+1),12)*F(b,e)
            actual=procession(e,b,F(1))
            assert actual<=ideal<native
    cuts=[thresholds(e,deep) for e in (5,7,11,13,17,19,23,29,31,37,41,43)
          for deep in (False,True)]
    result={'task':'C9-FIXED-GLUING-SWAP-20261025',
            'all_assertions_passed':True,'matrix_cases':cases,
            'explicit_bad_local_tate_realization':local_tate,
            'thresholds':cuts,'totals':{'integer_HNF_cases':len(cases),
                                     'tuple_formula_checks':checks,
                                     'prime_and_domain_threshold_cases':len(cuts)},
            'scope':{'tame_tensor_order_formula':'proved in natural-language record',
                     'common_packet_map':'source-relative deduction from III3.11(i)-(iii), not a claim that all APT is a set map',
                     'explicit_global_initial_theta_datum_constructed':False,
                     'global_archimedean_comparison_completed':False,
                     'original_P6_proved':False,'target_accepted':False}}
    out=Path(__file__).with_name('C9-TAME-SOURCE-SPAN-CERTIFICATE-20261025.json')
    out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    report=[]
    for item in cuts:
        if item['e']==41:
            report.append({k:v for k,v in item.items() if k!='residue_cases'})
    print(json.dumps({'all_assertions_passed':True,'totals':result['totals'],
                      'ell41':report,'target_accepted':False}))


if __name__=='__main__':
    main()
