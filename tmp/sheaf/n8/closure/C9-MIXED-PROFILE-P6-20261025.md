# C9 mixed bad/good profiles and the b=3 / b=273 P6 test

Task: task-303. Owner: qside. Date: 2026-10-25.
Short natural-language theorem/proof and exact obstruction; no Lean/Project
edits; no arbitrary rho; only this file written.

## 0. Verdict

The TAME Section 5 mixed bad/good profiles are genuinely larger (less negative)
than the all-bad rows.  Writing

    H_b(rho) := -(1/m) sum_{j=1}^m rho^{j+1}(s_j + 1/e),
    m=20, e=41, b j^2 = s_j e + t_j, 1 <= t_j < e,

the source lower bound is

    h_p^mixed(rho)/log p >= H_b(rho).                         (0.1)

For the all-bad positive-D profile the native q value is Q_p=-b/e log p.
Therefore the mixed finite image alone gives P6 at the local finite level iff

    H_b(rho) >= -b/e, i.e. F_b(rho) := -H_b(rho) <= b/e.     (0.2)

Numerically the thresholds F_b(rho)=b/e are

    b=3:   rho_* = 0.6916207660895637...,
    b=273: rho_* = 0.6680447184493201... .                    (0.3)

Thus mixed profiles exist with H_b(rho)>-b/e for a wide interval
0<rho<rho_*, including the TAME-proved rho<=1/2 interval.  The supremum of
the known lower bound is 0, approached as rho->0; it is not attained for a
nondegenerate mixed profile 0<rho<1.  In particular the finite h_p obstruction
of the all-bad b=273 row can be removed by a mixed profile in this interval,
but this does **not** by itself prove global P6.

The exact remaining obstructions are:
1. actual source/TC-B realization of a mixed profile with rho below the
   threshold (the source rho is not free);
2. the archimedean lower bound: global h_C >= h_p + h_inf, and no source lower
   bound h_inf>=... is available (task-270/278/287);
3. actual complete C/target hull and global good/other components.
No arbitrary rho is chosen.

## 1. Formula and monotonicity

TAME Section 5 gives, for a mixed bad/good profile with bad mass rho,

    h_p^aligned/log p >= H_b(rho),                             (1.1)
    H_b(rho) = -(1/m) sum_{j=1}^m rho^{j+1}(s_j+1/e).          (1.2)

Here s_j=floor(b j^2/e), m=(e-1)/2=20.  H_b is strictly decreasing in rho
(each term positive), with

    H_b(0)=0,   H_b(1)=-(1/m) sum_j(s_j+1/e).                  (1.3)

For b=3: sum_j s_j=200, H_3(1)=-(10+1/41)=-411/41=-10.02439...
For b=273: sum_j s_j=19100, H_273(1)=-(955+1/41)=-39156/41=-955.02439...
These are the all-bad A/B finite row scales (with the usual B-branch
correction for the aligned 9/41 row; the mixed bound is below that branch and
is used only as a lower bound).

The supremum over rho in [0,1] of the lower bound H_b is 0, approached at
rho=0; for 0<rho<1 there is no maximum (H_b strictly decreasing).  If rho=0
(all factors good) is treated as a degenerate endpoint, the maximum is 0, but
that is not a profile carrying the bad q-order b.

## 2. Finite P6 test

The positive-D all-bad profile has

    Q_p = -b/e log p.                                          (2.1)

The mixed finite image gives a lower bound for h_C:

    h_C >= (h_p^mixed + h_inf) >= (H_b(rho) + h_inf/log p) log p.  (2.2)

At the finite level (ignoring or nonnegative arch) h_C>=Q_p follows when

    H_b(rho) >= -b/e,   i.e. F_b(rho) <= b/e.                 (2.3)

TAME already proves (2.3) for rho<=1/2 using
s_j+1/e <= b j^2/e and the elementary bound on P_m(rho)=(1/m)sum j^2 rho^j.
The exact thresholds (2.0.3) are larger:

    b=3:   F_3(0.5)=0.005370235443 < 3/41=0.073170731707...,
           root rho_*=0.6916207660895637...;
    b=273: F_273(0.5)=0.982625770569 < 273/41=6.658536585...,
           root rho_*=0.6680447184493201....

For every 0<rho<rho_*, H_b(rho)>-b/e; at rho=rho_* equality.  Hence a mixed
finite image in this interval is itself enough to cover Q_p, even for b=273.
This is the positive finite-side rescue.

## 3. The archimedean term prevents an unconditional conclusion

The target hull is global:

    h_C >= h_p^mixed + h_inf.                                 (3.1)

Even when H_b(rho)>-b/e, a sufficiently negative h_inf can destroy P6.  The
exact arch threshold is

    h_inf/log p >= F_b(rho) - b/e.                            (3.2)

For rho<=1/2 this threshold is negative but small in magnitude:
b=3: F_3(1/2)-3/41=-0.0678...; b=273: F_273(1/2)-273/41=-5.676... .
No source theorem gives such a lower bound for h_inf.  Task-232 established
that the actual archimedean hull is not constructed; task-270/278/287 show the
B_I-zero container and product formula give no lower bound.  A lower bound
h_inf>=0 (e.g. B_I subset H_C,inf or a global unit in the hull) would suffice
for all rho in (0,rho_*), but is not available.

Thus mixed profiles remove the finite-positive-D obstruction, but not the
archimedean one.

## 4. Actual source status / exact obstruction

The following are not supplied by the frozen source:

(O1) an actual mixed profile with a source-determined rho in (0,rho_*):
     TAME Section 5 permits mixed bad/good tuples, but the actual C's rho is
     fixed by its source data; choosing rho would be arbitrary.

(O2) TC-B inclusion of the mixed possible-image region in H_C: this is
     definitional under the full possible-image union, but the actual complete
     C/H_C/BPS/Theta-gluing is not constructed (task-272/299).

(O3) the archimedean lower bound (3.2), or h_inf>=0: missing as above.

(O4) all other global components (good finite places, arch, Ind1/2/3, target
     column) and an actual complete C.

Consequently no unconditional P6 theorem follows for b=3 or b=273 from mixed
profiles.  For b=273, the all-bad counterexample is not robust: a mixed
profile with rho<0.6680 would put a region with h_p>-273/41 logp inside H_C,
so the finite deficit would disappear.  But without O1-O3 this is a
conditional scenario, not a constructed counterexample-free or
counterexample-positive theorem.

## 5. Supremum / maximum summary

    sup_{0<=rho<=1} H_b(rho) = 0   (approached at rho->0; not attained for
                                     0<rho<1),
    max over the degenerate rho=0 endpoint = 0,
    H_b(1) = -411/41 (b=3), -39156/41 (b=273),
    finite P6 interval: 0<rho<=rho_*,
    rho_*(b=3)=0.6916207661..., rho_*(b=273)=0.6680447184....

For the alternative convention where Q scales with rho as Q_p=-rho b/e log p
(the mixed q itself), the corresponding roots are about 0.66277 (b=3) and
0.62987 (b=273), still well above 1/2.  The qualitative conclusion is the same:
small mixed bad mass beats the q value; the actual source rho and the
archimedean lower bound are the blockers.

## 6. Conclusion

Mixed bad/good profiles do provide a genuine new positive finite image: their
normalized height H_b(rho) is larger than the all-bad rows for 0<rho<1, and
for rho<=rho_* it exceeds Q_p=-b/e logp even for b=273.  This is a valid
conditional route to P6 at the finite level and shows the all-bad b=273
negative row is not the whole H_C.

It does not give an unconditional P6 theorem because:
- the actual source rho is not chosen freely and no complete C with a mixed
  profile is constructed;
- TC-B/actual H_C is conditional;
- the archimedean lower bound h_inf>=F_b(rho)-b/e (or at least h_inf>=0) is
  not available.

No arbitrary rho or archimedean radius was chosen.  target_accepted=false;
P6 remains open/conditional.

## 7. Sources

- C9-TAME-LOG-DOMAIN-20261025.md, Section 5, formula (15) and the rho<=1/2
  comparison.
- C9-TARGET-GENERATED-20261025.md, Section 2.2, mixed profiles in H_C.
- C9-ARCH-LOWER-S3-20261025.md / C9-ARCH-LOWER-NEW-20261025.md /
  C9-ARCH-S3-BIREGION-20261025.md, arch lower-bound obstructions.
- C9-B3-P6-ASSEMBLY-20261025.md, conditional b=3 P6 assembly and signs.
