# C9 new source theorem: global unit or B_I in the archimedean hull

Task: task-249. Owner: kummer. Date: 2026-10-25.
Stage: SHEAF stage1 new source theorem/construction attempt, natural-language.
No Lean/Project edits, no new attack, no target changes. Only this file written.
target_accepted=false; P6 open.

## 0. Inputs

- C9-NEW-ARCH-THRESHOLD-20261025.md (task-248), 271 lines,
  SHA256 9c51eb90cf5d316d6649dca376139f885175b56a283bfd05ef80a4608dab332e.
- C9-ARCH-HULL-20261025.md (task-240), 134 lines,
  SHA256 e2a12e952811c21959fb61e9308a40ae7b1b5d6c5916d6aed4abc1920dd45ce7.
- C9-ARCH-ACTUAL-RINF-20261025.md (task-232), 319 lines,
  SHA256 6ac23b85163e11706f8e26d96671437d8cfe80953fe5ba535bba92fd5b15f236.
- C9-ARCH-GLOBAL-20261025.md (task-149), 198 lines,
  SHA256 524e078ad85c72067627f006d165a724436e1ba508e86475c5f991860586e489.
- Kondo 2025/2026 local snapshots for E_j/F/K/E[6] data,
  SHA256 ff39006cf92ec22e1a39caa89fee9b86080953861d7ac6405e6919338c5c9e6f
  and fe7c464e2ae09ffc85c4b02cad8b10b7eebef351113975a34c53a62169a27d86.

Binding: B_I-zero normalization log-volume(B_I)=0; h_inf(C) is the
archimedean log-volume with radial readout log r_v and angular term;
IV container: H_C,inf subset pi^{j+1}B_I at level j (IUT IV Prop1.5(iii)(iv)).
The threshold is S3=(12/41)log12301=2.7563226845..., so the desired lower
bound is h_inf>=-S3.

## 1. Verdict

This file tests the three candidates. None is proved from the frozen source;
the main result is a precise obstruction to each and a conditional
product-formula reduction.

- **T3b (B_I subset H_C,inf): NOT PROVED; no IV contradiction.** The IV
  container is H_C,inf subset pi^{j+1}B_I. Since pi=3.14...>1, we have
  B_I subset pi^{j+1}B_I, so B_I subset H_C,inf is consistent with the
  container; IV gives only the opposite upper inclusion. B_I-zero sets
  log-volume(B_I)=0 and does not assert B_I subset H_C,inf. If T3b were
  proved, h_inf>=0 would follow; the source does not prove it.
- **T3a (qUnit/E[6]/theta global unit in H_C,inf): NOT PROVED; exact
  obstruction.** qUnit is a local finite q-pilot unit, not a global element
  with archimedean components; E[6] torsion points are global over F but there
  is no source map E[6](C)/E_j(C)->H_C,inf; the archimedean hull is not a
  subset of F or of E_j(C). A global unit (e.g. i in F) is not known to lie in
  H_C,inf. The product formula would give h_inf>=0 only for a global unit whose
  archimedean profile is contained in the hull as a unit ball/region, which is
  not supplied.
- **T3c (global point with finite valuation sum<=S3 in H_C,inf): NOT PROVED;
  same missing map**, plus no canonical global point with the required
  valuation is constructed. qUnit has the wrong local/global status; E[6]
  torsion has no source archimedean-hull image and no computed finite
  valuation sum.

No target-compatible proof of h_inf>=-S3 is obtained. The genuine new
conditional theorem is the product-formula reduction (Theorem 6.1); T3a, T3b,
and T3c all remain conditional on a missing unit/point/B_I-to-hull map.
No candidate is shown impossible; T3b is consistent with IV and simply
unconstructed.

## 2. Definitions and the IV container

At level j, the archimedean tensor packet has j+1 factors. Under IV:

    H_C,inf subset pi^{j+1} B_I,   logvol(pi^{j+1}B_I)=(j+1)log pi.   (2.1)

with B_I-zero logvol(B_I)=0. The archimedean readout is

    h_inf(C)=sum_v alpha_v [h_v^ang(A_v)+log r_v],  sum_v alpha_v=1.   (2.2)

The target upper bound is h_inf<=A_arc=((l+5)/4)log pi=11.5log pi=13.164393687...
for l=41; at maximal level j=20, 21log pi=24.039327603....

The wanted lower bound is h_inf>=-S3=-2.7563226845...; both bounds are
compatible with the IV upper bound, so the threshold is not excluded by IV.

## 3. T3b: B_I subset H_C,inf

The IV container is

    H_C,inf subset pi^{j+1} B_I.                                   (3.1)

Since pi=3.14159...>1, pi^{j+1}B_I is **larger** than B_I, and
B_I subset pi^{j+1}B_I. Therefore the IV container is perfectly compatible
with B_I subset H_C,inf; there is no scaling contradiction. The source gives
only the upper inclusion (3.1), not the lower inclusion.

If T3b held, then log-volume monotonicity and B_I-zero give

    h_inf(C) >= logvol(B_I)=0.                                     (3.2)

So T3b is a legitimate sufficient condition for h_inf>=0. But it is not a
consequence of B_I-zero, and it is not stated in IV or Kondo. B_I-zero is a
normalization of the reference unit ball, not a statement about the possible
image hull.

The exact missing source statement is

    (BIH) B_I subset H_C,inf                                         (3.3)

for the actual archimedean Theta-pilot possible-image hull. Neither (3.1) nor
B_I-zero implies (BIH); the converse is also not a source theorem. T3b is
therefore **conditional/open**, not impossible and not proved.

## 4. T3a: global units, qUnit, E[6] torsion

### 4.1 Product-formula reduction

Let u be a global unit u in F^times (or K^times), and let (u_v)_v be its
archimedean absolute values. The product formula for a global unit gives

    sum_{v|infty} alpha_v log|u|_v = 0,                            (4.1)

because all finite valuations of a unit vanish (weighted by alpha_p). If the
archimedean profile of u is contained in H_C,inf as a **unit ball/region**
(not merely one point), then h_inf>=0; more generally, if H_C,inf contains a
region R_u of normalized log-volume >=sum alpha_v log|u|_v, then
h_inf>=sum alpha_v log|u|_v=0.

If one only knows a single point u in the hull, the point does not by itself
give a log-volume lower bound without an angular/radial containment. This is a
technical correction to the informal statement "point in hull => h_inf>=0";
the correct hypothesis is a unit ball/region inclusion, or the radial
product-formula criterion.

### 4.2 qUnit

The q-pilot unit qUnit is constructed at the bad finite place p=12301 as a
local q-parameter unit. It is not a global element of F: it has finite-place
data but no canonical archimedean embeddings/profile. There is no source map
from qUnit to H_C,inf. The same applies to qCandidate at finite level: it is a
finite local unit, not a global unit with a product-formula archimedean side.

Therefore T3a with qUnit is not a source theorem; it is a category error
(local finite unit vs global archimedean hull).

### 4.3 E[6]/theta torsion units

E[6] is a finite etale group scheme over F (Kondo/E_j skeleton), and E[6](C)
gives archimedean torsion points of the classical elliptic curve. But the
archimedean Theta-pilot hull H_C,inf is not the classical E_j(C) or its torsion
set; task-232 proves there is no source map

    E_j(C), periods, torsion, or theta values -> H_C,inf.            (4.2)

Moreover, E[6] torsion points are not global **units** (their coordinates are
not units in F), so (4.1) does not apply directly; one would need their finite
valuation sum and archimedean profile, both missing. Thus E[6] does not supply
T3a either.

### 4.4 A global unit such as i

F contains i=zeta_4, a global unit with |i|_v=1 at all archimedean places. Its
finite valuations are zero, so product formula gives h_inf>=0 **if** the
archimedean image of i lies in H_C,inf as a unit ball/region. There is no
source theorem identifying the number-field embedding i with a point of the
Theta-pilot archimedean hull. H_C,inf is a tensor-packet possible-image set, not
a subset of F. This is the exact missing map.

## 5. T3c: a canonical global point with finite valuation sum<=S3

T3c would need a canonical global point x (unit, torsion, or controlled
non-unit) with

    sum_p alpha_p v_p(x) log p <= S3,                               (5.1)

whose archimedean image lies in H_C,inf. The product formula then gives

    h_inf >= -sum_p alpha_p v_p(x) log p >= -S3.                    (5.2)

Candidate checks:

- qUnit: finite local unit at p, but not global; no archimedean image; its
  finite valuation sum is not a global weighted sum.
- E[6] torsion: global over F, but its finite valuation sum is not computed,
  its archimedean profile is not mapped to H_C,inf, and torsion coordinates are
  not units.
- i: global unit with finite sum0 (<=S3) and archimedean modulus1, but no map
  to H_C,inf; if a unit ball around its image were in the hull, (5.2) would
  give h_inf>=0.
- p^{-1} or a q-pilot root: would give a negative finite valuation sum, but
  such a point is not constructed as a global element and is not known to lie
  in H_C,inf; choosing it by hand is exactly the arbitrary-point assumption
  prohibited by the task.

Thus T3c is a valid **conditional criterion** but not a source theorem. The
missing data are (i) a canonical global point, (ii) its finite valuation sum,
and (iii) its archimedean possible-image containment.

## 6. New conditional theorem (T3-cond)

Theorem 6.1 (product-formula hull lower bound). Assume there is a global point
x in F^times and a region R_x subset H_C,inf whose normalized log-volume is at
least sum_v alpha_v log|x|_v, with

    sum_p alpha_p v_p(x) log p <= S3.                              (6.1)

Then

    h_inf(C) >= -S3.                                              (6.2)

Proof. Product formula for x gives
sum_arch alpha log|x| + sum_p alpha v_p(x)log p=0. The hull volume is at least
the archimedean profile sum, so
h_inf>=sum_arch alpha log|x| = -sum_p alpha v_p(x)log p >= -S3. QED.

This theorem is **conditional** on the region inclusion and the valuation
bound. It does not assume B_I subset H_C,inf (which is not supplied by IV) and
does not choose an arbitrary point.

## 7. Proved / conditional / impossible

Proved:

- IV upper bound h_inf<=A_arc=13.164393687... under target containment.
- IV container is compatible with B_I subset H_C,inf because
  pi>1 and B_I subset pi^{j+1}B_I; T3b is not excluded by IV.
- Product-formula conditional theorem 6.1.
- qUnit is a finite local object, not a global unit; no source archimedean map.
- E[6]/E_j(C)/periods/torsion have no source map to H_C,inf (task-232).

Conditional/missing:

- T3a: a global unit (e.g. i) in H_C,inf as a unit ball/region; missing
  unit-to-hull map.
- T3b: B_I subset H_C,inf; missing (BIH), and B_I-zero/IV do not supply it.
- T3c: a canonical global point with finite valuation sum<=S3 in H_C,inf;
  missing point, valuation, and hull containment.
- h_inf>=-S3: not proved; would follow from T3a/T3b/T3c/6.1.

Impossible:

- Deriving h_inf>=D_3 (or any D>A_arc) inside IV (task-240); this does not
  apply to the weaker threshold -S3.
- Deriving a global unit/point from qUnit alone.
- E_j(C)/torsion as a substitute for H_C,inf without a source map.
- Any argument that assumes B_I subset H_C,inf and calls it proved.

No impossibility is established for T3a/T3b/T3c themselves at the threshold
-S3; they are unconstructed source theorems.

## 8. Conclusion

The new source theorem attempt does not prove h_inf>=-S3. T3b is consistent
with the IV container (because pi>1), so it is not impossible; it simply is
not supplied by B_I-zero or IV. T3a and T3c are conditional on a missing
canonical global-unit/point-to-hull map and, for T3c, on an uncomputed finite
valuation sum. The product-formula theorem 6.1 is the honest conditional
reduction: it would give h_inf>=-S3 from a canonical global point/region, but
no such source point or B_I inclusion is constructed.

The B=I b=3 corridor therefore remains conditional/open; no lower bound
h_inf>=-S3, no counterexample, and no target closure follows. No arbitrary
points, no ad hoc r_v, and no U/B normalization are used.

No Lean/kernel closure; P6 open; target_accepted=false.

## 9. Status

- Natural-language source-theorem attempt only; no Lean/Project edits.
- T3a/T3b/T3c exact obstructions and conditional product-formula theorem
  recorded; T3b is consistent with IV but unconstructed; no h_inf lower bound.
- target_accepted=false.
