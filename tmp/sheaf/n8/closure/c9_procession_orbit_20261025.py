"""Exact orbit/hull calculations with an explicit fixed target container.

These verify ordinary tensor-region mathematics.  They do not certify that
this interpretation of the orbit has been reconciled with all IUT source
comparisons; in particular they do not certify the original P6 target.
"""
from fractions import Fraction as F
from itertools import product, permutations
from math import prod
from pathlib import Path
import json


PRIMES = (5,7,11,13,17,19,23,29,31,37,41,43)
DISTRIBUTIONS = (
    ((F(0),F(1,2)),(F(10),F(1,2))),
    ((F(0),F(1,5)),(F(2,3),F(3,10)),(F(7,2),F(1,2))),
    ((F(2),F(1)),),
    ((F(1),F(2,5)),(F(4),F(3,5))),
)


def push_tuple(t, sigma):
    result = [None]*len(t)
    for old, new in enumerate(sigma):
        result[new] = t[old]
    return tuple(result)


def inverse(sigma):
    out = [None]*len(sigma)
    for old,new in enumerate(sigma):
        out[new]=old
    return tuple(out)


def expected_min(distribution, r):
    levels = sorted(set(a for a,w in distribution))
    last, answer = F(0), F(0)
    for level in levels:
        tail = sum((w for a,w in distribution if a>=level), F(0))
        answer += (level-last)*tail**r
        last = level
    return answer


def exact_fixed_target_orbit(distribution, r):
    n, j = len(distribution), r-1
    tuples = list(product(range(n),repeat=r))
    weights = {t:prod(distribution[v][1] for v in t) for t in tuples}
    seed = {t:j*j*distribution[t[-1]][0] for t in tuples}
    hull = {t:None for t in tuples}
    branch_log_volumes = []
    permutations_checked = 0
    for sigma in permutations(range(r)):
        image = {}
        for old in tuples:
            new = push_tuple(old, sigma)
            image[new] = seed[old]
            assert weights[new] == weights[old]
        assert set(image) == set(seed)
        branch_log_volumes.append(-sum((weights[t]*image[t] for t in tuples), F(0)))
        for t in tuples:
            hull[t] = image[t] if hull[t] is None else min(hull[t],image[t])
        # If the target frame is moved too and then pulled back, no new region.
        pulled_back = {old:image[push_tuple(old,sigma)] for old in tuples}
        assert pulled_back == seed
        permutations_checked += 1
    mean = sum((a*w for a,w in distribution),F(0))
    assert set(branch_log_volumes) == {-j*j*mean}
    for t in tuples:
        assert hull[t] == j*j*min(distribution[v][0] for v in t)
    log_hull = -sum((weights[t]*hull[t] for t in tuples),F(0))
    assert log_hull == -j*j*expected_min(distribution,r)
    gain = log_hull+j*j*mean
    assert gain >= 0
    assert (gain > 0) == (len(set(a for a,w in distribution))>1)
    return {"r":r, "tuples":len(tuples), "permutations":permutations_checked,
            "branch_log_volume_per_log_p":str(-j*j*mean),
            "hull_log_volume_per_log_p":str(log_hull),
            "gain_per_log_p":str(gain)}


def procession_injections():
    checked = 0
    for r in range(1,7):
        injections = set(permutations(range(r+1),r))
        for k in range(8):
            sig = tuple((i+k)%r for i in range(r))
            tau = tuple((i+k)%(r+1) for i in range(r+1))
            invsig = inverse(sig)
            transported = {tuple(tau[f[invsig[i]]] for i in range(r))
                           for f in injections}
            assert transported == injections
            checked += len(injections)
    return checked


def p_m(m,rho):
    return sum((j*j*rho**j for j in range(1,m+1)),F(0))/m


def threshold(m):
    lo,hi=F(0),F(1)
    for _ in range(48):
        middle=(lo+hi)/2
        if p_m(m,middle)<=1:
            lo=middle
        else:
            hi=middle
    assert p_m(m,lo)<=1<p_m(m,hi)
    return {"lower":str(lo),"upper":str(hi),"decimal_midpoint":float((lo+hi)/2)}


def procession_case(ell):
    m=(ell-1)//2
    for j in range(1,m+1):
        images={(j+k)%(j+1) for k in range(m+1)}
        assert images==set(range(j+1))
    rho=F(1,2)
    bernoulli_hull=-sum((j*j*rho**(j+1) for j in range(1,m+1)),F(0))/m
    bernoulli_seed=-rho*F(ell*(ell+1),12)
    native=-rho
    assert bernoulli_hull>=native>bernoulli_seed
    # A uniform positive valuation is not improved by any pure permutation.
    uniform_hull=-F(ell*(ell+1),12)
    assert uniform_hull<-1
    return {"ell":ell,"m":m,"full_branch_family_size":m+1,
            "two_place_largest_tuple_count":2**(m+1),
            "half_bad_seed_per_a_log_p":str(bernoulli_seed),
            "half_bad_hull_per_a_log_p":str(bernoulli_hull),
            "half_bad_native_per_a_log_p":str(native),
            "uniform_hull_per_a_log_p":str(uniform_hull),
            "sharp_mass_threshold_for_fixed_target_orbit":threshold(m)}


def main():
    small=[]
    for d in DISTRIBUTIONS:
        assert sum(w for a,w in d)==1
        small.append({"distribution":[[str(a),str(w)] for a,w in d],
                      "cases":[exact_fixed_target_orbit(d,r) for r in range(2,6)]})
    checked_injections=procession_injections()
    cases=[procession_case(ell) for ell in PRIMES]
    for m in range(2,201):
        assert p_m(m,F(1,2))<1
    # Four-dimensional literal ideals. Ordered coordinates (0,0),(0,1),(1,0),(1,1).
    M=F(10)
    I=[F(0),M,F(0),M]
    flipped=[F(0),F(0),M,M]
    hull=[min(a,b) for a,b in zip(I,flipped)]
    vol_I=-sum(I)/4
    vol_hull=-sum(hull)/4
    average_with_one_rounding_unit=vol_I+1
    assert (vol_I,vol_hull,average_with_one_rounding_unit)==(F(-5),F(-5,2),F(-4))
    assert vol_hull>average_with_one_rounding_unit
    diagnostic={"M":str(M),"seed_ideal_exponents":list(map(str,I)),
                "flipped_ideal_exponents":list(map(str,flipped)),
                "hull_ideal_exponents":list(map(str,hull)),
                "branch_log_volume":str(vol_I),"hull_log_volume":str(vol_hull),
                "mean_based_bound_plus_one":str(average_with_one_rounding_unit),
                "is_complete_IUT_counterexample":False}
    result={"task":"C9-PROCESSION-ORBIT-20261025","all_assertions_passed":True,
            "small_exact_orbits":small,"procession_cases":cases,"four_dimensional_diagnostic":diagnostic,
            "totals":{"distributions":len(DISTRIBUTIONS),"exact_orbit_cases":16,
                      "injection_transports_checked":checked_injections,
                      "prime_processions":len(cases),"half_mass_checks":199},
            "scope":{"fixed_target_orbit_theorem":"proved in natural-language record",
                     "source_compatibility_with_IV_average_bound":"unresolved; do not count the orbit as an accepted complete-source escape",
                     "original_P6_proved":False,"target_accepted":False}}
    out=Path(__file__).with_name('C9-PROCESSION-ORBIT-CERTIFICATE-20261025.json')
    out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps({'all_assertions_passed':True,'totals':result['totals'],
                      'ell41':next(c for c in cases if c['ell']==41),
                      'diagnostic':diagnostic,'target_accepted':False},ensure_ascii=False))


if __name__=='__main__':
    main()
