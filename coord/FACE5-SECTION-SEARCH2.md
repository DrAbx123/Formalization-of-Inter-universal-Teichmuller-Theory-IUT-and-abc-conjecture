# FACE5-SECTION-SEARCH2 — rational-function section search (l=5)

Status: model-level linear feasibility. qpilot's SSINEQ-ANATOMY.md is still absent; numbers
use the A893/A892 data and the lana theta-scaling exponent (j+1)^2. Not a Lean/lana theorem.

## 1. Ansatz

Section:
    x = (prod_j theta_j^{a_j}) * r,   r in K^×,   j=1,2 (nC=2),
where theta_j has finite exponent j^2 and archimedean norm controlled by j^2.
Variables:
- a_1, a_2 in R (or Z);
- u_p := ord_p(r) for each bad finite place p, arbitrary integers in the number-field
  normalization, subject to the principal-divisor (product-formula) constraint
      sum_v [k_v:Q] * ord_v(r) = 0.
The archimedean ord_v(r) is not independent: it is fixed by the product formula once the
finite u_p are chosen.

Number of variables for bad {2,11}: a_1,a_2,u_2,u_11 plus one arch value = 5.
Constraints: two finite target equations plus one product-formula equation = 3.
=> real solution space dimension = 2 (before positivity), versus rank 1 in A909.

## 2. Finite coefficients (q=22)

ord_2(q)=ord_11(q)=1, so
    c_{1,p}=1, c_{2,p}=4,  L := a_1 + 4a_2  (same for p=2 and p=11; 1/(2l) omitted).
Finite target equations:
    L + u_2  = f_2,
    L + u_11 = f_11,
where the per-place targets are
    f_p = hullPacket_p - (sF-1) * A_p,   sF-1 = 1.5,  A = absLogQ = log22/10.
hullPacket_2 = 0.519860 (A893 p=2 finite term), hullPacket_11 = 0 (odd finite term).

The split A_p is not fixed by the total target. Two natural allocations:

### Allocation A — proportional to ord_p(q) log p / logQ
    A_2 = A*log2/log22 = 0.069315, A_11 = A*log11/log22 = 0.239790,
    (sF-1)A_2 = 0.103972, (sF-1)A_11 = 0.359684,
    f_2 = 0.519860 - 0.103972 = +0.415888,
    f_11 = 0 - 0.359684 = -0.359684.
Then the arch target is
    f_arch = (V - (sF-1)A) - f_2 - f_11 = 1.491303,
which is exactly the A892 arch term.
But f_11 < 0, so the exact finite target at p=11 violates finite-norm positivity.

### Allocation B — all (sF-1)A charged to p=2
    (sF-1)A_2 = 0.463656, (sF-1)A_11 = 0,
    f_2 = 0.519860 - 0.463656 = +0.056204,
    f_11 = 0.
Then f_arch = 1.491303 again, and both finite targets are nonnegative.

Allocation B is the positivity-compatible choice in this model; it is a choice of how the
global requirement is assigned to places, not a derived identity.

## 3. Exact real solution (allocation B)

Choose a_1=a_2=0 (theta factor trivial), then
    u_2 = f_2 = 0.056204,
    u_11 = f_11 = 0,
so the finite equations are solved exactly. The arch ord is fixed by the product formula:
    u_arch = -(u_2 log2 + u_11 log11)/log? = -0.056204 * log2 / (normalization),
which is absorbed in the arch term; in log-volume units the total is
    f_2 + f_11 + f_arch = 0.056204 + 0 + 1.491303 = 1.547507 = V - (sF-1)A.
Thus **exact real solution exists** in allocation B, with zero residual and all finite norms
nonnegative.

General real solution: any L with u_2=f_2-L, u_11=f_11-L; the arch value adjusts by the
product formula. The two-dimensional family is (a_1,a_2) modulo the one relation
L=a_1+4a_2, plus the arbitrary L; equivalently u_2,u_11 are free subject to
u_2-u_11=f_2-f_11.

## 4. Integer ord model

If u_p must be integers while a_j stay real:
- allocation B targets f_2=0.056204, f_11=0, so the difference f_2-f_11=0.056204 is not
  an integer. Hence u_2-u_11 cannot be an integer equal to it.
- The best integer choice is u_2=u_11=0, then L must approximate both f_2 and f_11;
  least-squares gives L*=(0.056204+0)/2=0.028102, finite residual +-0.028102.
  The arch term can still absorb the total (f_arch=1.491303 unchanged), so the total sum
  can be matched exactly by the arch degree of freedom, but per-place finite matching has
  residual 0.0281.
- If one insists on exact finite matching with integer u, allocation B is not exactly
  attainable; allocation A also has a non-integer difference (-0.775572), so the same
  obstruction holds.

## 5. Dimension and residual summary

| model | variables | constraints | dimension | exact per-place finite? | positivity | residual |
|---|---|---:|---:|---|---|---|
| A909 theta only | a1,a2 | 2 finite + arch | rank 1, no exact | no | yes if L>0 | LS L*=0.5158, RMSE 0.4195 |
| + r, real u (alloc B) | a1,a2,u2,u11,uarch | 2 finite + product | 2 | YES | YES | 0 (per-place); total exact |
| + r, integer u (alloc B) | a1,a2,u2,u11 in Z, uarch | same | 0 (for this target) | no | yes (choose u=0) | finite +-0.0281; total exact via arch |

## 6. Verdict

- Adding r removes the rank-1 obstruction: with real ordinates, exact per-place finite
  matching is possible, with a 2-dimensional solution family and the product formula
  absorbing the arch value.
- Positivity requires the global requirement be allocated so that finite targets are
  nonnegative (allocation B; proportional allocation A gives f_11<0 and fails positivity).
- With integer ordinates, per-place exact matching fails by a residual of 0.0281 in
  allocation B; the total V-(sF-1)A can still be matched exactly via the arch term.
- Therefore the section search **has a solution in the real-relaxed model**, is
  **conditionally feasible with integer ordinates** (residual 0.0281 per finite place), and
  the remaining obstruction is the integer/product-formula compatibility plus the
  allocation of the requirement among places.

Caveat: qpilot's SSINEQ-ANATOMY.md and compiled explicit D are still absent; this is a
model linear-algebra result, not a lana/Lean theorem.
