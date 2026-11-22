# C9 new archimedean lower-bound attempt: h_inf >= -S3

Task: task-278. Owner: qside. Date: 2026-10-25.
Stage: short natural-language theorem/proof and exact obstruction; no Lean/
Project edits; no arbitrary r_v or arbitrary hull point; only this file written.

## 0. Verdict

The b=3 B=I threshold remains

    S3 = (12/41) log 12301 = 2.7563226845469613...,
    F_B=I,b=3 = -S3 - h_inf,
    F<0  <=>  h_inf > -S3.

A **new angle** was tried: use the identity/zero-label Gaussian action or a
canonical global unit/point to force a point or the unit ball into the actual
archimedean Theta-pilot hull.  It does not give a source theorem.  The exact
obstruction is the same missing object as task-270, but the new candidates fail
for explicit structural reasons:

1. the zero label/constant splitting is not a Theta-pilot output;
2. A^0=id is an action identity, not a permitted pilot output;
3. a global unit (i, root of unity, 1) has no proved map into H_C,inf;
4. the product formula applies to points already in the hull, not to an
   arbitrary region or to B_I;
5. the IV container has the opposite inclusion direction.

No h_inf>=-S3 is proved.  The corridor remains conditional/open.  No arbitrary
r_v or point is introduced.

## 1. Short conditional theorem (valid, but hypothesis missing)

Let H_C,inf be the actual archimedean possible-image hull, with radial radii r_v
and angular term h_v^ang(A_v), under B_I-zero:

    h_inf = sum_{v|infty} alpha_v [h_v^ang(A_v) + log r_v].

Theorem 1.  If either

(A) B_I subset H_C,inf, or
(B) a global unit u in F^times lies in H_C,inf, or
(C) a global point x in F^times lies in H_C,inf with
    sum_p alpha_p v_p(x) log p <= S3,

then h_inf >= -S3.

Proof.  (A) B_I-zero gives logvolume(B_I)=0; monotonicity of normalized volume
for the inclusion B_I subset H_C,inf gives h_inf>=0>=-S3.  (B) Product formula
for the global unit u: sum_v alpha_v log|u|_v=0, and h_inf >= sum_v alpha_v
log|u|_v because u lies in the hull; hence h_inf>=0.  (C) Product formula for x:
sum_v alpha_v log|x|_v = -sum_p alpha_p v_p(x)log p, and h_inf is at least the
left side because x lies in the hull; the displayed finite bound <=S3 gives
h_inf>=-S3.  QED.

This theorem is correct but useless for the actual source until (A), (B), or
(C) is proved.  Task-270 already recorded that none is in the frozen corpus.

## 2. New candidate 1: identity/zero-label action

In the fixed Gaussian realization, the generator is

    g_{r,v,j} = zeta_{r,v,j} a^{j^2},   j=1,...,(l-1)/2,

with zeta a root-of-unity ambiguity.  The Gaussian monoid has nonnegative powers
and A^0=id; the zero label separates the constant unit part.  One might try:

    A^0 applied to the integral unit region S gives S itself;
    if S is the unit ball B_I, then B_I subset H_C,inf;
    hence h_inf>=0.

Why this is not a source theorem:

- The allowed Theta-pilot labels are j=1,...,(l-1)/2; j=0 is not an allowed
  pilot output.  The zero label is used for the constant/splitting part, not to
  generate a new pilot image.
- The source explicitly warns that the monoid contains all natural powers but
  not every power is an allowed output of the same pilot.  Taking A^0 as a
  possible image is therefore an extra admissibility assumption.
- Even if S were allowed, identifying S with B_I is not part of the source; the
  integral reference S is a source input that may be a different unit region or
  its image.
- The IV container is H_C,inf subset pi^{j+1}B_I, not B_I subset H_C,inf.

Thus the identity-action route does not produce (A).  It would be an arbitrary
choice of output, not a theorem.

## 3. New candidate 2: global unit i / root of unity / 1

F contains i; i is a global unit.  If i (or 1, or a root of unity) were in
H_C,inf, Theorem 1(B) would give h_inf>=0.

Obstruction:

- H_C,inf is a subset of an archimedean tensor packet (Theta-pilot possible
  images), not the set of field elements F or E_j points.
- There is no source map F^times -> H_C,inf, no theorem that the tensor-packet
  identity is an allowed output, and no theorem that the constant/unit part of
  the Gaussian monoid contributes a hull point.
- E_j's E[6] rational points and i are curve/field data; E_j(C) periods/torsion
  have no source map to the IUT archimedean hull (task-232).
- Choosing any of them as a hull point would be arbitrary.

Therefore no global unit in H_C,inf is proved.

## 4. New candidate 3: canonical global point and product-formula region

The natural product-formula idea is to use a global point x in the hull with
small finite valuation sum.  The q-pilot has v_p(q)=6>0, the opposite sign; the
p^{-1} log-shell normalization is a construction step, not a global point in
the hull.  A canonical point 1 has finite valuation sum 0 and would give
h_inf>=0 by Theorem 1(C), but its hull membership is exactly the missing map of
Section 3.

A "product-formula region" version would need an integration/averaging identity
over a positive-measure region, not a point.  The product formula is a pointwise
identity; applying it to a region requires a point or a measure-theoretic
argument not present in the source.  The hull volume is not the integral of the
pointwise product formula over the possible-image region, and no such identity
is proved.  Hence no region lower bound follows.

## 5. Exact obstruction theorem

Theorem 2 (obstruction).  The frozen source does not prove any of:

(i) B_I subset H_C,inf;
(ii) existence of a global unit in H_C,inf;
(iii) existence of a canonical global point x in H_C,inf with
     sum_p alpha_p v_p(x) log p <= S3;
(iv) a direct hull lower bound h_inf>=-S3.

Consequently h_inf>=-S3 is not available.

Proof.  The actual archimedean possible-image set H_C,inf is not constructed
(task-232); only the IV upper container and B_I-zero normalization are present.
The IV inclusion direction is H_C,inf subset container, not reverse.  The
Gaussian/Theta-pilot labels do not include j=0, the identity action is not an
allowed output, and the zero label is a constant splitting, not a hull point.
No map from global units/points or E_j torsion/periods to H_C,inf exists.
Product formula requires a point already known to be in the hull.  Therefore
none of (i)-(iv) follows.  QED.

Corollary.  The b=3 B=I corridor is not closed; neither F<0 nor F>=0 is proved
for an actual C.  No counterexample to P6 is produced.

## 6. What a genuine new proof would require

A new source theorem must do one of:

1. prove B_I subset H_C,inf from the actual Theta-pilot values (a lower
   sharpness/containment statement, not the IV upper container);
2. construct a source map from a canonical global unit/torsion point (1, i,
   E[6], etc.) into H_C,inf, with the map compatible with the pilot action;
3. prove an integrated product-formula/region identity giving a hull lower
   bound without a preselected point;
4. construct H_C,inf and compute its normalized volume directly.

None is present.  Adding any of them as a hypothesis is a new source theorem,
not a consequence of current data.

## 7. Status

No h_inf>=-S3 proof.  The new identity/unit/region candidates are explicitly
obstructed; the old task-270 obstruction remains binding.  No arbitrary r_v,
hull point, or normalization is used.  target_accepted=false; P6 open.

Inputs: C9-ARCH-LOWER-S3-20261025.md (SHA 3847F1DEE3F3F73322A2F5F74E5ECC936E3FF0113BA3319FF76EA1D20904F73F),
C9-ARCH-ACTUAL-RINF-20261025.md (SHA 6AC23B85163E11706F8E26D96671437D8CFE80953FE5BA535BBA92FD5B15F236),
C9-BPS-THETA-REGION-NATURAL-RESEARCH-20261024.md (j=1..(l-1)/2 and zero-label
warning), C9-ARCH-HULL-20261025.md (IV/general container).
