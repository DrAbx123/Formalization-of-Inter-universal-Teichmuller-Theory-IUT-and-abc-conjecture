# C9 negative global weights and branch-independent contradiction

Task: task-239 (New-math exploration: negative global weights and
branch-independent contradiction). Owner: volumedet. Date: 2026-10-25.
Stage1 natural-language/construction exploration. No arbitrary assumptions,
no Lean/Project/target edits. Only this file written. `target_accepted=false`.

Inputs/context: C9-MASTER-CONTRADICTION-20261025.md, C9-ERROR-LEDGER-20261025.md,
C9-FULLC-WEIGHTS-ATTACK-20261025.md, C9-AGGREGATE-BI-ATTACK-20261025.md,
C9-AUDIT-AGGREGATE-BI-20261025.md, C9-ARCH-NORMALIZATION-CORRECTION-20261025.md,
C9-OTHER-LOCAL-TYPES-ATTACK-20261025.md, C9-MOD41-EXACT-G-20261025.md.

## 0. Verdict

The residual inequality is

    Delta := Q_C - h_C <= D_C^Sp - h_inf(C),                   (0.1)

where D_C^Sp is the conditional finite bad residual. For the b=3,p=12301
B=O_K branch,

    D_3 = (408/41) log 12301 = 93.71497127459669...,
    A   = (l+5)/4 log pi = 13.164393687268102...,
    D_3 - A = 80.55057758732859... > 0.                         (0.2)

Thus the archimedean upper bound alone leaves a positive residual; no
contradiction. The new-math question is whether some genuine source
contribution can be negative enough to make `D_C^Sp-h_inf<=0`.

Answer under the current corrected corpus: **no branch-independent actual
contribution does this**.

- Degree weights alpha_p are nonnegative; no actual negative global weight
  exists. Arbitrary negative weights can be written down but violate the
  fixed normalization and do not correspond to a complete C.
- Good finite places contribute 0 relative to the reference; tensor-order
  losses are nonnegative and reduce h_C (i.e. worsen Delta); Ind1
  permutations, Ind2 and Ind3 do not add positive normalized volume.
- Other local types (wild/e!=ell) have nonpositive absolute restricted-shell
  volume; the normalization shift Delta_shell is not an actual output hull
  and cannot be inserted into h_C.
- Archimedean h_inf is bounded above by A, independent of the radius, and
  A < D_3.
- B=I b=3 is the only conditional local surplus (`12/41 log p`); it is
  branch-dependent, not actual under the natural trace alignment, and has no
  constructed complete C.
- A branch-independent minimax must use the worst branch B=O_K, which gives
  D_3-A>0; therefore no branch-independent contradiction follows.

The exact negative route is blocked by missing source construction, not by a
new inequality. The detailed sign audit follows.

## 1. Sign conventions and the closure criterion

Assume the conditional assembly (CFTH + TC-A..H + TC-S + the finite donor
formulas) and define

    Delta(C)=Q_C-h_C,
    R(C)=D_C^Sp-h_inf(C).

Then Delta(C)<=R(C). A contradiction to a counterexample Delta>0 would
follow from R(C)<=0; positivity of R(C) is not itself a contradiction. For
the b=3 branch,

    R(C) = D_3 - h_inf(C) >= D_3 - A >0,                       (1.1)

because h_inf(C)<=A is the paper-level upper bound (B_I-zero normalization).
So the displayed data are consistent with Delta>0; no closure.

If one instead wants a global **lower** bound showing Delta>0 for every C
(a counterexample), the sign is the opposite: one needs a lower bound on
D_C^Sp or an upper bound h_inf; neither is available as an actual theorem.
This file only explores closure/contradiction, not a counterexample.

## 2. Sign audit of every proposed contribution

### 2.1 Bad B=O_K places

Under the conditional aligned formula, for every b>0,

    Q_p - h_p = d_p log p >0,   d_p=Q_p-h_p in log-p units;
    d_3=408/41,  d_273=38883/41.                         (2.1)

Adding another B=O_K bad place adds another positive `d_p log p` to
D_C^Sp; it can only worsen the residual. This is proved algebraically under
the conditional formulas; it is not an actual target theorem.

### 2.2 Bad B=I places

For b=3, B=I gives

    h_B=9/41,  Q_p=-3/41,  Q_p-h_B=-12/41 <0.

Thus the local contribution is negative, i.e. it can **reduce** D_C^Sp by

    S(p)=(12/41) log p.                                  (2.2)

This is the only finite negative contribution in the current corpus. It is
conditional: B=I is not actual under the natural trace alignment; it requires
nonzero v/full barGamma, and the branch itself is type-gapped in the full
source. It is not a branch-independent contribution.

For b=273 B=I is still negative residual: `-38736/41` vs Q=-273/41 gives
deficit 38463/41; B=I does not help there.

### 2.3 Good finite places

At a good selected place the Gaussian profile is the unit and the tensor hull
is the reference O_E; its normalized contribution relative to the reference
is 0. Q_C contains only bad places. No positive contribution and no negative
D_C contribution comes from good finite places. If a good place is moved by a
permutation, the contribution is still 0, not positive.

### 2.4 Tensor-order/integral-closure terms

The tensor order D_r differs from the integral closure O_{E_r} by a
nonnegative length; the normalized log-volume loss is

    delta_r=(r-1)(e-1)/(2e) >=0.                          (2.3)

It is subtracted from h_C, so it makes h_C smaller and Delta larger; it
cannot help closure. Full Ind1 alignment removes this loss in the conditional
aligned formula, but it does not create a positive contribution beyond that
formula.

### 2.5 Kummer zero/unit-small domain

The Kummer zero path carries the integer lattice O_K; the small-unit domain
exp(pz) gives pO_K and normalized hull O_K (relative volume 0). It can shrink
the local region but cannot increase h_C beyond the reference and cannot
produce a negative D_C contribution.

### 2.6 Ind1 permutations, Ind2, Ind3

- Full Ind1 is the procession automorphism group, not finite label
  translation. Pure factor permutations change the tuple/min threshold; the
  conditional permutation hull is bounded by the original average and does
  not add positive normalized volume. Target use requires TC-A..H/TC-S.
- Ind2 Ism/order-2 preserves the integer lattice; it can move the target hull
  branch but no positive normalized volume is proved (TC-H missing).
- Ind3 log-link indeterminacy is upper semi-compatible; it does not add
  positive volume beyond the allowed branch. The second log-link on the same
  log-image path is empty for all e.

### 2.7 Other local types (wild/e != ell, e >= p-1)

Under the corrected log-domain analysis, the absolute restricted-shell
volume is

    logvol_O(I_K^res) = ((n_exp-e) f/e) log p <=0,
    n_exp=floor(e/(p-1))+1, equality only e=1 or (p=3,e=2).  (2.4)

Larger f makes this more negative, not positive. The only nonnegative
quantity is the normalization shift

    Delta_shell = ((n_exp-1) f/e) log p <= (f/(p-1)) log p.   (2.5)

Delta_shell is a shift toward zero relative to the tame shell; it is not an
actual output-hull theorem and no source theorem inserts it into h_C. To
cover the b=3 conditional D_3 one would need

    f >= (p-1)*408/41 = 122400;

and for b=273 f>=11,664,900. No source bound or actual realization of such f
is available. This is a missing/conditional branch, not compensation.

### 2.8 Archimedean place

Under the binding B_I-zero normalization, h_inf=log r_inf for F=Q and the
paper-level container upper bound is A=13.164393687268102. Since
h_inf<=A<D_3, the archimedean place cannot close the b=3 residual. If h_inf
is negative, the residual is larger; a negative h_inf is not a compensating
contribution. The Lean readout sign (`absLogAddHom=-log`) is a convention
flip, not an actual negative global weight; it must be converted before any
comparison.

## 3. Negative global weights: actual vs arbitrary

The degree weight is

    alpha_p=[(F_mod)_p:Q_p]/[F_mod:Q] >=0,   sum_{p|p0} alpha_p=1.  (3.1)

All alpha_p are nonnegative; alpha_inf=d_v/[F:Q]>0. There is no actual
negative global weight in the fixed normalization. Canonical-vs-normalized q
conversion multiplies by the positive degree d=[F_v:Q_p] (tame case d=41), not
by a negative sign; the archimedean Lean sign is also a convention, not a
weight.

### 3.1 What an arbitrary negative weight would do

If one allowed arbitrary real alpha_p with sum 1 (not source-allowed), one
could make the residual negative by assigning a negative weight to a
positive-defect place. For example with one b=3 B=O_K place,

    D_C = alpha_p D_3 + ...

and choosing alpha_p<0 would turn the largest positive term negative. But
this violates (3.1), the degree normalization, the product formula, and the
fixed native q/BPS/gluing setup; it does not correspond to an admissible
complete C. It is an arbitrary assumption, not a construction.

### 3.2 No source-derived negative weight

To derive a negative global weight from the source one would need a negative
degree or a negative normalization factor. The degree weights are indices of
local fields; they are positive integers divided by [F:Q]. The canonical q
factor d is positive. The only sign flips are convention flips (paper
positive radial log-volume vs Lean negative additive readout). Therefore
negative global weights are **impossible** under the fixed source
normalization.

## 4. Branch-independent minimax over B=O_K/B=I

For a bad place p let beta_p in {O_K,I} be the branch choice and

    D_C(beta)=sum_p alpha_p (Q_p-h_p(beta_p)) + (other finite terms).

Under the current conditional formulas:

- beta_p=O_K contributes +d_p log p>0;
- beta_p=I, b=3 contributes -S(p)<0;
- beta_p=I, b=273 contributes +38463/41 log p>0.

With a b=3,p=12301 O_K place,

    D_C(beta) >= D_3 - (number of B=I b=3 places) S(12301)
                 for the displayed configuration,

and the archimedean bound gives

    R(beta) >= D_3 - N S - A.                             (4.1)

For N=0 this is 80.55>0; for N>=30 (and the actual h_inf near A) it can
become negative. The count 30 is the conditional aggregate threshold;
N>=34 is the strict gross threshold. Thus:

- the **best case for closure** is B=I at many b=3 places, which is
  conditional, requires distinct primes and actual v/full barGamma, and is
  not branch-independent;
- the **worst case for closure** is B=O_K at all places, which is compatible
  with the current source and gives R>0;
- a branch-independent contradiction/closing statement must hold for the
  worst branch; it therefore fails.

Equivalently, the minimax

    max_{beta} R(C,beta) >= D_3-A>0                     (4.2)

for any C with the b=3 O_K place. Since a branch-independent statement
cannot choose beta, no conclusion R<=0 follows. The min over beta may be
negative only through conditional B=I; this is a branch-dependent hypothesis,
not a theorem.

## 5. Attempts to construct negative contributions

1. **Negative alpha_p.** Impossible under degree normalization (3.1);
   arbitrary negative weights are excluded.
2. **Good finite places with negative h.** Good h is 0 relative to the
   reference; if tensor order is included it is negative and worsens Delta.
   No construction gives a positive h at a good place.
3. **Tensor/integral-closure loss as a negative term.** delta_r>=0 reduces
   h_C, hence increases Delta; it cannot help.
4. **Ind1 permutation/minimax.** Permutation hull is bounded by the original
   average; it does not produce a negative D_C term. Full Ind1 target use
   requires TC conditions.
5. **Ind2 Ism/Ind3 log.** No positive normalized volume; branch movement
   does not supply a negative D_C term.
6. **Other local types with large f.** Delta_shell is not actual and the
   absolute shell volume is negative; f thresholds 122400 / 11664900 are
   unconstructed. No source bound gives them.
7. **Archimedean radius.** h_inf<=A; A<D_3; increasing the radius cannot
   exceed the paper-level container bound A. Negative h_inf worsens Delta.
8. **Many B=I b=3 places.** Conditional arithmetic; needs 30/34 places for
   b=3, 3236/3241 for b=273, or one huge prime above the thresholds; no
   actual S_bad/B=I/v/barGamma/TC construction. It is not branch-independent.
9. **Negative global weights from q canonical/normalized conversion.** The
   factor d is positive (41 in the tame case), not negative; the Lean sign
   flip is a convention. No source-derived negative weight.

None of 1-9 produces an actual negative contribution that is
branch-independent.

## 6. Actual / conditional / impossible / open

PROVED / exact algebra (under the named conditional formulas):

- alpha_p>=0 and sum alpha_p=1 in the fixed degree normalization;
- good finite contribution 0; tensor loss delta_r>=0; Ind1/Ind2/Ind3 no
  positive volume; other-local shell volume <=0; arch h_inf<=A;
- D_3=93.714971..., A=13.164393..., D_3-A=80.550577...>0;
- B=O_K local contribution positive for every b>0;
- B=I b=3 local contribution -12/41 log p (conditional formula);
- branch-independent minimax bound (4.2) with B=O_K.

CONDITIONAL:

- finite D_C^Sp values, B=O_K/B=I actuality, H_A-full, B=I aggregate,
  other-local Delta_shell, F_sem degree, TC-A..H/TC-S, actual arch h_inf;
- all uses of the residual formula as an actual target inequality.

IMPOSSIBLE as source construction:

- actual negative degree weights under the fixed normalization;
- actual positive compensation from good/tensor/Ind1/Ind2/Ind3;
- actual positive absolute other-local shell volume;
- archimedean-only closure for b=3/273 (A<D);
- branch-independent closure/contradiction using B=O_K;
- using arbitrary negative weights or arbitrary bad sets.

OPEN/MISSING:

- actual complete C with S_bad, H_A-full, full barGamma matrices, B branch;
- actual B=I realizations and aggregate prime choices;
- actual other-local types/f; actual archimedean hull/radius;
- TC target container and fixed q volume class;
- any global contradiction or counterexample.

## 7. New-math conclusion

The natural negative route is sign-blocked at the actual B=O_K branch:
`D_3-A>0`, and every actual source contribution available in the corrected
corpus is zero or positive-to-Delta (tensor loss makes Delta larger).
The only negative finite term is the conditional B=I b=3 surplus, which is
branch-dependent, type-gapped at full source level, and requires a
constructed aggregate. Therefore:

    no negative global weight is actual;
    no branch-independent contradiction follows;
    a conditional B=I aggregate could close only branch-dependently;
    the full P6 remains open.

This is a negative result about the current route, not a proof of P6 and not
a complete-C counterexample.

## 8. Status

Stage1 natural-language/exact-arithmetic exploration only. No new arbitrary
assumption, no Lean/Project edits. Only this file written.
`target_accepted=false`; complete C9/P6 not proved.
