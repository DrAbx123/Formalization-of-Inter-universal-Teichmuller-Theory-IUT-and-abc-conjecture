"""Exact additive-span certificates; no full IUT source-admission claim.

For odd p, K=Q_p[x]/(x^2-p), D=O_K tensor_Zp O_K.
The integral closure E=K x K uses the embeddings y=x and y=-x.
All computations use integers, determinant minors, and p-adic valuations.
"""
from itertools import combinations
from fractions import Fraction as F
from pathlib import Path
import json


def mm(a, b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def power(a, n):
    out=identity(len(a))
    for _ in range(n):
        out=mm(out,a)
    return out


def det(a):
    a=[row[:] for row in a]
    sign, previous=1,1
    for k in range(len(a)-1):
        if a[k][k] == 0:
            t=next((t for t in range(k+1,len(a)) if a[t][k]),None)
            if t is None:
                return 0
            a[k],a[t]=a[t],a[k]
            sign=-sign
        pivot=a[k][k]
        for i in range(k+1,len(a)):
            for j in range(k+1,len(a)):
                numerator=a[i][j]*pivot-a[i][k]*a[k][j]
                assert numerator % previous == 0
                a[i][j]=numerator//previous
        for i in range(k+1,len(a)):
            a[i][k]=0
        previous=pivot
    return sign*a[-1][-1]


def vp(n,p):
    if n == 0:
        return None
    n=abs(n)
    answer=0
    while n%p == 0:
        n//=p
        answer+=1
    return answer


def span_index(matrix,p):
    vals=[]
    for cols in combinations(range(len(matrix[0])), len(matrix)):
        value=det([[row[c] for c in cols] for row in matrix])
        if value:
            vals.append(vp(value,p))
    assert vals
    # DVR determinantal ideal of a full-rank generated lattice.
    return min(vals)


def holomorphic_hull_index(matrix,p):
    answer=0
    for offset in (0,2):
        values=[]
        for a,b in zip(matrix[offset],matrix[offset+1]):
            if a:
                values.append(2*vp(a,p))
            if b:
                values.append(2*vp(b,p)+1)
        assert values
        answer+=min(values)
    return answer


def test_case(p,M):
    # D-basis: 1, x, y, xy.  E-basis: (1,x) in each of its two fields.
    B=[[1,0,0,p],[0,1,1,0],[1,0,0,-p],[0,1,-1,0]]
    X=[[0,p,0,0],[1,0,0,0],[0,0,0,p],[0,0,1,0]]
    Y=[[0,0,p,0],[0,0,0,p],[1,0,0,0],[0,1,0,0]]
    assert vp(det(B),p) == 1
    Xm,Ym=power(X,M),power(Y,M)
    matrix=mm(B,[a+b for a,b in zip(Xm,Ym)])
    exponent=span_index(matrix,p)
    expected=2*M+(1 if M%2 == 0 else 0)
    assert exponent == expected
    assert holomorphic_hull_index(matrix,p) == 2*M
    # A strict lower bound from a common transport uses a universal theorem;
    # these GL_4(Z_p) shears are diagnostics, NOT declared source-allowed maps.
    T=identity(4)
    least_hull=2*M
    for depth in range(1,21):
        row=(depth*3)%4
        other=(row+1+(depth%3))%4
        shear=identity(4)
        shear[row][other]=(-1 if depth%2 else 1)*(depth+p)
        T=mm(shear,T)
        assert det(T) == 1
        transported=mm(T,matrix)
        assert span_index(transported,p) == exponent
        h_index=holomorphic_hull_index(transported,p)
        assert h_index <= exponent
        least_hull=min(least_hull,h_index)
    return {"p":p,"M":M,"span_index_in_integral_closure":exponent,
            "span_log_volume_per_log_p":str(-F(exponent,4)),
            "source_hull_log_volume_per_log_p":str(-F(M,2)),
            "common_transport_depths_checked":20,
            "largest_observed_target_hull_log_volume_per_log_p":str(-F(least_hull,4))}


def main():
    cases=[test_case(p,M) for p in (3,5,7,101) for M in range(13)]
    result={"task":"C9-PROCESSION-ORBIT-20261025-additive-span",
            "all_assertions_passed":True,"cases":cases,
            "totals":{"ramified_tensor_lattices":len(cases),
                      "common_transport_composites":20*len(cases),
                      "depth":20},
            "exact_formula":"nu(sum(x^M D,y^M D))/log(p) = -M/2 - (1/4 if M is even else 0)",
            "scope":{"universal_common_transport_lower_bound":"proved in natural-language record",
                     "GL_diagnostics_are_source_admission_certificates":False,
                     "complete_fixed_BPS_common_transport_constructed":False,
                     "original_P6_proved":False,"target_accepted":False}}
    out=Path(__file__).with_name('C9-ADDITIVE-SPAN-CERTIFICATE-20261025.json')
    out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps({"all_assertions_passed":True,"totals":result['totals'],
                      "sample":cases[0:3],"target_accepted":False},ensure_ascii=False))


if __name__ == '__main__':
    main()
