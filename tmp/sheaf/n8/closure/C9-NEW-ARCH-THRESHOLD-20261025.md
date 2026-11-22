# C9 actual archimedean h_inf and the b=3 B=I threshold -S3

Task: task-248. Owner: qside. Date: 2026-10-25.
Stage: natural-language/exact-source research only; no Lean/Project edits; no
arbitrary r_v; no U/B ad hoc; only this file written.

## 0. Verdict

The threshold needed by the conditional b=3 B=I counterexample corridor is

    S3 = (12/41) log 12301 = 2.7563226845469613...,
    threshold: h_inf > -S3 = -2.7563226845469613....

At profile level

    F_B=I,b=3(C) = Q_C - h_C = -S3 - h_inf(C),
    F < 0  <=>  h_inf > -S3.

**No target-compatible lower bound h_inf >= -S3 is available from the current
source skeleton.** In particular:

- B_I-zero is a normalization (log-volume(B_I)=0), not an inclusion
  B_I subset H_C,inf and not a lower bound h_inf >= 0;
- the IV container gives only the upper bound h_inf <= A_arc = 11.5 log pi
  = 13.164393687...;
- the shell container gives only the weaker upper bound h_inf <= log pi under
  the unproved shell containment;
- no actual archimedean hull H_C,inf or radial/angular data is constructed;
- E_j periods/torsion/theta values have no source map to H_C,inf;
- no global point (unit, torsion, or controlled finite-valuation point) is
  known to lie in H_C,inf, so the product formula gives no lower bound.

Therefore the B=I b=3 corridor remains conditional/open: h_inf could be above
or below -S3 as far as current target-compatible data show. No counterexample
and no positivity theorem follows.

## 1. Inputs and binding conventions

Inputs:

- C9-ARCH-ACTUAL-RINF-20261025.md, SHA256
  6AC23B85163E11706F8E26D96671437D8CFE80953FE5BA535BBA92FD5B15F236;
- C9-ARCH-HULL-20261025.md, SHA256
  E2A12E952811C21959FB61E9308A40AE7B1B5D6C5916D6AED4ABC1920DD45CE7;
- C9-NEW-VARIATIONAL-COUNTEREXAMPLE-20261025.md, SHA256
  100AF6DF5D98B850E1F13D9E259EF360E7D1B70B64F3C7753A038EBAFC3DCBA3;
- C9-AGGREGATE-BI-ATTACK-20261025.md, SHA256
  62156BD5D334BD417BF9D0161EEE00B53897380C56FB565FC572B9BBB6C6F515;
- C9-AUDIT-UNIT-FILTRATION-20261025.md, SHA256
  8D715581577F057C151CC7023B98F5A896A04121EFC32D13B6EBAEF21C563E09.

Binding conventions:

- B_I-zero: log-volume(B_I)=0; local radial readout log r_v; global weights
  alpha_v=d_v/[F:Q], sum alpha_v=1; shell-pi formulas withdrawn.
- h_inf(C) = sum_v alpha_v [h_v^ang(A_v) + log r_v]; angular retained.
- A_arc=((l+5)/4)log pi for l=41 is 11.5 log pi=13.164393687..., an upper
  bound, not a lower bound.
- All finite B=I/B=O_K branch assignments are conditional; task-208 showed
  the full-Out filtration premise fails, and task-245 states B=I is not
  realized by the E_j skeleton.

## 2. Exact B=I b=3 arithmetic

Uniform profile: F_mod=Q, one rational bad p=12301, e=41, b=3; conditional
finite B=I values

    h_fin = (9/41) log p,
    Q_p = (-3/41) log p,
    F = Q_p - h_fin - h_inf
      = -(12/41) log p - h_inf
      = -S3 - h_inf,
    S3 = (12/41) log 12301 = 2.7563226845469613...,
    -S3 = -2.7563226845469613....

Hence:

- h_inf=0 gives F=-2.7563226845<0;
- h_inf>-S3 gives F<0;
- h_inf=-S3 gives F=0;
- h_inf<-S3 gives F>0.

The IV upper bound only says h_inf<=A_arc=13.1644; it is compatible with both
sides of -S3. The shell upper h_inf<=log pi=1.1447 is also compatible with both
sides. Neither yields a sign for F.

## 3. What B_I-zero does and does not imply

Normalization:

    mu^log(B_I)=0,   mu^log(pi^{j+1}B_I)=(j+1)log pi.

It does **not** imply any of:

- B_I subset H_C,inf;
- h_inf >= 0;
- H_C,inf contains a unit ball or global unit;
- h_inf >= -S3.

B_I is the integral-structure reference used to normalize log-volume. The
actual possible-image hull may be much smaller than B_I; then h_inf is
negative. Conversely, if one could prove

    B_I subset H_C,inf,

then monotonicity would give h_inf>=0, hence F<=-S3<0 and a counterexample in
this profile. But this inclusion is not a theorem of IV Prop1.5/Thm1.10: those
give the **container** pi^{j+1}B_I for possible images, not a lower inclusion
B_I in the image hull. No other source theorem supplies it.

Similarly, if the actual hull contains a global unit u (all finite valuations
zero), the product formula gives h_inf>=0; if it contains a global torsion
point, the same. But:

- the archimedean Theta-pilot possible-image set is not constructed;
- E[6] rational over F does not imply E[6] lies in the tensor-packet hull;
- no map from E_j torsion points to H_C,inf exists;
- choosing a torsion point as a hull point would be arbitrary.

## 4. What the IV container actually gives

IV Prop1.5(iii)(iv)/Thm1.10(vii): if archimedean factors lie in the length-pi
shell, the tensor product lies in

    pi^{j+1} B_I,   h_inf,j <= (j+1) log pi,

and after procession average

    h_inf <= A_arc = 11.5 log pi = 13.164393687....

Both are **upper** bounds. They do not exclude h_inf>-S3; the container allows a
large positive h_inf. They also produce no positive lower bound.

At the container maximum the conditional B=I b=3 value is

    F = -S3 - A_arc = -2.7563226845 - 13.1643936873
      = -15.9207163718...,

the most negative known profile value, but it is not attained by a constructed
C.

## 5. Available conditional lower-bound mechanisms

### 5.1 Hull contains B_I

    B_I subset H_C,inf  =>  h_inf>=0  =>  F<=-S3<0.

Status: not proved; no source theorem; B_I-zero alone does not give it.

### 5.2 Hull contains a global unit or torsion point

If x in H_C,inf has v_p(x)=0 for all finite p, then log r_v>=log|x|_v and the
product formula gives

    h_inf >= sum_v alpha_v log|x|_v = 0.

Status: no actual point of H_C,inf is known; E_j E[6] is not mapped into the
archimedean tensor hull. Conditional only.

### 5.3 Hull contains a global point with controlled finite valuations

For x in H_C,inf, the product formula gives

    h_inf >= -sum_p alpha_p v_p(x) log p.

The threshold -S3 follows from

    sum_p alpha_p v_p(x) log p <= S3 = (12/41)log12301.

Status: no such source point in H_C,inf is constructed. The E_j q-pilot has
positive bad valuation v_p(q)=6, giving the opposite sign; the p^{-1} log-shell
normalization is a construction step, not a global possible-image point.

### 5.4 Large-capsule construction

To force h_inf>=D with shell-radius factors one needs k>=D/log pi; for D_3,
k>=82, while the target has at most j+1<=21 factors. Such a construction
exceeds the IV container and is outside the target, not a lower bound for the
actual H_C,inf. This is task-240's quantitative impossibility for positive D.

## 6. Why no actual lower bound is available from E_j

The E_j skeleton supplies:

- actual elliptic curve equation and local p=12301 data;
- field skeleton F=Q(i,E[6],F_sem), K=F(E[41]);
- formal C_K/C_F/V/epsilon definitions;
- all archimedean places of F/K are complex because i in F.

It does not supply:

- explicit archimedean embeddings of F/K;
- the actual archimedean Theta-pilot possible-image set;
- a map from E_j(C), its periods, torsion points, or theta values into H_C,inf;
- radial radii r_v or angular regions A_v of H_C,inf;
- any global point/unit/torsion in H_C,inf.

Classical uniformization E_j(C)=C/Lambda_tau is analytic data of the elliptic
curve, not the IUT archimedean hull. The period ratio is non-CM and not
explicit; even a numerical period would not identify source possible images.
Therefore r_v=|period|, r_v=max|torsion|, r_v=1, or r_v=pi would be arbitrary
assignments and are not used.

## 7. B=I branch itself is not actual

Even if a target-compatible lower bound h_inf>-S3 were available, it would not
give a counterexample by itself: B=I is a conditional finite branch. Task-245
states B=I is not realized by the E_j skeleton; task-208 showed the full-Out
filtration/integrality route for one B=O_K argument fails; the full B branch
remains undetermined. A genuine counterexample needs:

1. an actual complete C;
2. an actual B=I realization in that C;
3. an actual archimedean hull with h_inf>-S3;
4. all TC-A..TC-H and TC-S target-container conditions.

None is available. The b=3 B=I corridor is a conditional scenario, not a
constructed counterexample.

## 8. Exact / conditional / missing

Exact:

- S3=(12/41)log12301=2.7563226845469613...;
- F_B=I,b=3=-S3-h_inf; F<0 iff h_inf>-S3;
- B_I-zero normalization; A_arc=11.5 log pi=13.164393687...;
- all archimedean places of F/K are complex (contains i);
- E_j finite/local data and conditional B=I table.

Conditional:

- actual complete C, B=I branch, target-container inclusion;
- IV upper and shell upper bounds;
- any B_I subset hull / global-unit / global-point lower-bound mechanism;
- archimedean hull from E_j periods (not source-defined).

Missing/unavailable:

- actual archimedean hull H_C,inf and r_v/angular term;
- target-compatible lower bound h_inf>=-S3;
- containment B_I subset H_C,inf;
- global unit/torsion/point in H_C,inf;
- actual B=I realization and complete C;
- proof of F<0 or F>=0 in the B=I b=3 corridor.

## 9. Conclusion

h_inf>-S3 is exactly what the B=I b=3 profile needs for F<0, but the current
source gives only upper bounds and no actual archimedean hull. The three
plausible lower-bound mechanisms (B_I subset H_C,inf; a global unit or torsion
in the hull; a global point with controlled finite valuations) are all unproved
and unsupported by the E_j skeleton. The large-capsule mechanism is outside the
IV target container. Therefore the lower bound is **unavailable**, not
constructed; the corridor is not closed and no counterexample is produced.

This is a source-relative unavailability statement, not a proof that no actual
hull in another construction could have h_inf>-S3. target_accepted=false; P6
remains open. No arbitrary r_v was introduced.

## 10. Sources

- C9-NEW-VARIATIONAL-COUNTEREXAMPLE-20261025.md: F=-S3-h_inf and B=I corridor.
- C9-ARCH-HULL-20261025.md: IV container, A_arc, large-capsule impossibility,
  product-formula conditional criteria.
- C9-ARCH-ACTUAL-RINF-20261025.md: E_j archimedean missing data.
- C9-AUDIT-UNIT-FILTRATION-20261025.md: non-actual full-Out filtration premise
  and B=I conditional status.
- C9-AGGREGATE-BI-ATTACK-20261025.md: S3 arithmetic.

End of C9-NEW-ARCH-THRESHOLD-20261025.
