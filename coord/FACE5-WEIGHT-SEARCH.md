# FACE5-WEIGHT-SEARCH — linear feasibility of theta weights (l=5)

Status: model-level linear-algebra audit. qpilot's SSINEQ-ANATOMY.md is still absent;
the coefficient model below is the one induced by the lana theta-scaling formula
(componentVol_scaleElt: exponent (j+1)^2) and the A893 local data. Not a Lean/lana theorem.

## 1. Setup

l=5 => nC=(5-1)/2=2 capsules, indexed j=1,2 (zero-based j=0,1).
Unknown weights a_1, a_2 in R (or Z), representing
    x = theta_1^{a_1} * theta_2^{a_2},
with theta_j having finite exponent j^2 and archimedean norm controlled by j^2.

For each bad place p, the finite local coefficient is
    c_{j,p} = j^2 * ord_p(q)     (common factor 1/(2l) omitted),
and the archimedean row is the same shape (up to a common scalar s):
    c_{j,inf} = s * j^2 * log|q|_inf.
The target vector is fixed by
    sum_v (-log||x||_v) = V - (sF-1)A,
with V=2.011163, A=logQ/10, logQ=log22=3.091043, so V-(sF-1)A=1.547507.

Distribute the target over places as
    f_2 = 0.519860 (finite p=2 hull term),
    f_11 = 0        (odd p=11 finite hull term),
    f_inf = 1.027647 (=1.547507 - 0.519860 - 0).
These are the A893/hull numbers, not independent measurements.

## 2. Linear system (q=22, bad {2,11})

q=22 has ord_2(q)=ord_11(q)=1. Therefore the coefficient rows for p=2 and p=11 are
identical:

    p=2:   a_1 + 4 a_2 = 0.519860
    p=11:  a_1 + 4 a_2 = 0
    inf:   s*(a_1 + 4 a_2) = 1.027647

The first two equations are inconsistent: same left side, different right sides.
For any s != 0, all three rows are scalar multiples of the same linear form
L = a_1 + 4a_2, so the system has **no exact solution in (a_1,a_2)**.

Rank: 1 (one independent row), two unknowns => one-dimensional solution set for any chosen
right-hand side; the per-place targets require three different values of L, impossible.

## 3. Least squares

Minimize over L = a_1 + 4a_2 (the arch scalar s cancels in the normal equations if all
rows are proportional):
    (L - 0.519860)^2 + (L - 0)^2 + (L - 1.027647)^2.
The normal equation gives
    L* = (0.519860 + 0 + 1.027647)/3 = 0.515836.
Residuals:
    p=2:   +0.004024
    p=11:  +0.515836
    inf:   -0.511811
Sum of squares: 0.0000162 + 0.266087 + 0.261951 = 0.528054.
Root mean square residual: sqrt(0.528054/3) = 0.4195.
Sign pattern: (+ , + , -): the p=11 finite row is the large positive residual; the arch row
is the compensating negative one.

Real weights: any (a_1,a_2) with a_1+4a_2=0.515836 is a least-squares solution, e.g.
(a_1,a_2)=(0.515836,0) or (0,0.128959).
Integer weights: a_1+4a_2 must be an integer; the nearest choices are 1 or 0.
- L=1: residuals (0.480140, 1, -0.027647); SSE=0.230534+1+0.000764=1.231298, RMSE=0.6407.
- L=0: residuals (-0.519860, 0, -1.027647); SSE=0.270254+0+1.056058=1.326312, RMSE=0.6649.
So there is no exact integer solution and the best integer L is 1 (SSE 1.2313), still far
from zero.

## 4. Positivity of finite norms

The achieved finite norm is N_p = L (same for both places). The least-squares value
L*=0.5158 is positive, so all finite norms are >=0; positivity is satisfied.
But the price is that p=11 has norm 0.5158 instead of the target 0 and p=2 has 0.51986
instead of 0.51584. Exact per-place data cannot be met.
If one instead enforces the p=11 target L=0, then p=2 misses by 0.51986; the finite norms
remain nonnegative, so positivity alone does not rule out the weight ansatz — the
inconsistency is in the per-place targets.

## 5. Diagnosis and extra freedom

The rank-1 structure comes from q=22 having the same order at both bad primes and from
using only the common scaling j^2. With two weights and two finite places of equal
coordinate, the target vector is overdetermined.

Needed extra degrees:
1. a place-dependent basis (e.g. include the local different/arch term as a separate
   coordinate, not a common j^2 multiplicity); or
2. allow a constant/torsion term (one scalar) added to all rows; or
3. use theta values with different exponents at 2 and 11 (non-equal ord_p(q)), making the
   two finite rows non-proportional; or
4. allow independent weights per place (a_{j,p}), which makes the system trivially solvable
   but loses the global theta-product interpretation.

## 6. Verdict

- Exact linear system: **NO solution** for two weights (rank 1 vs three target rows with
  different values); no exact integer solution either.
- Least-squares real solution: L*=0.515836; residual norm 0.4195 (SSE 0.528054); sign
  pattern (+,+,-).
- Finite positivity: satisfied (L*>0).
- The missing direction is a genuine extra degree of freedom (place-dependent different/
  torsion term or non-equal ord_p(q)); this is the concrete "gap" of the weight ansatz.

Caveat: qpilot's SSINEQ-ANATOMY.md and a compiled explicit D are still absent; coefficients
are the model induced by the lana theta-scaling exponent (j+1)^2 and A893 data.
