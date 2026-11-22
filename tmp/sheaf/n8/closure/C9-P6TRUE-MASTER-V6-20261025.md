# C9 P6-true master v6: branch audit synthesis

Task: task-366. Owner: multiradial. Date: 2026-10-25.
Natural-language master/audit synthesis only. No mixed/E3; no Lean/Project
edits. Deliverable: this file only. target_accepted=false; P6 open.

## 0. Verdict

The branch audit changes the P6-true master. The shortcut

    "both B=O_K and B=I are possible images, so R_B subset H_C independent of
     the actual branch"

is FALSE/NOT STATED in the source. H_C is the hull of the actual
Ind1/Ind2/Ind3 possible-image orbit of the fixed C, and the B branch is
determined by the actual barGamma/Out action. Only the actual branch is a
source possible image; the two abstract row lattices are not simultaneously
present.

The arch audit also corrects the stronger shortcut:

    "B_I is an archimedean possible image, so B_I subset H_C,inf and h_inf>=0"

is NOT a source theorem. IV gives the opposite container inclusion
H_C,inf subset pi^{j+1}B_I and B_I-zero normalization; it does not give
B_I subset H_C,inf. h_inf>=0 is conditional on that missing inclusion.

P6-true master v6 is therefore:

    E1 (no admissible complete b=273 C)
    + actual B=I branch (kappa in [1,40]) with R_B subset H_C
    + [B_I subset H_C,inf  OR  h_inf>=-S3]
    => b=3 B=I P6; b=273 excluded by E1.

If the actual branch is B=O_K, the R_B/H_B route is unavailable; B=O_K b=3
would require h_inf>=D3=93.714971>A_proc, impossible under the IV arch bound.
No unconditional P6 proof is obtained.

## 1. Sign and local arithmetic

p=12301, e=41, fixed F_mod=Q uniform profile, F(C)=Q_C-h_C.

    P6 target: h_C>=Q_C  <=>  F(C)<=0.                            (1.1)
    F>0: counterexample; F<0: P6 holds; F=0: boundary.

b=3:

    Q_p=(-3/41)log p,
    H_A=(-411/41)log p, H_B=(9/41)log p=2.067242013...,
    D_3=(408/41)log p=93.7149712746...,
    S_3=(12/41)log p=2.7563226845....

b=273:

    Q_p=(-273/41)log p,
    H_A=(-39156/41)log p, H_B=(-38736/41)log p,
    D_A=(38883/41)log p=8931.174578603...,
    D_B=(38463/41)log p=8834.703284644....

Arch B_I-zero: h_inf<=A_proc=11.5 log pi=13.164393687... (upper only).

C1/C3:

    h_C >= sum_p alpha_p H_p^Sp log p + h_inf,                     (C1)
    F=Q_C-h_C <= D_C^Sp-h_inf.                                    (C3)
C1 lower on h_C; C3 upper on F. E48 sign correction remains binding.

## 2. Branch audit: actual branch only

Source result (TAME Section 6 + IUT Ind1/Cor3.12; task-362):

    B = closed Zp-span union_{alpha in actual Gamma} alpha(O_K).
    B=O_K iff barGamma preserves l=O_K/J;
    B=I  iff some actual gamma moves l.
    B=O_K: L_A=sum_i p^s pi_i D_r;
    B=I:   L_B=p^{s-r+1}J^{tensor r}.

This is a classification of the ACTUAL Gamma/barGamma, not of an abstract
union of both branches. H_C is the hull of the actual source possible-image
orbit, not the hull of "all abstract B branches". The source does not state
that both L_A and L_B occur for one fixed C, nor that H_C contains both.

Consequences:

  - Actual B=I + TC-B: L_B is an actual possible-image family; R_B subset H_C
    is legitimate; h_C>=H_B+h_inf.
  - Actual B=O_K: only L_A is actual; L_B is not an actual possible-image
    family, even though L_A subset L_B abstractly. R_B subset H_C is not
    available from this argument.
  - The "both branches possible images" assumption would make R_B subset H_C
    independent of kappa, but it is a branch-choice/profile change, not a
    source theorem. It is excluded.

Exact missing branch input (G-B): an actual B=I realization/generator whose
barGamma moves l=O_K/J and whose L_B family is an actual possible image of the
fixed C (equivalently kappa=e*vp(Tr y1)-vpi(y1) in [1,40]).

## 3. Arch audit: B_I possible image and h_inf>=0

IV/arch gives only:

    H_C,inf subset pi^{j+1}B_I,
    logvol(B_I)=0,
    h_inf<=A_proc.

B_I-zero is a normalization/reference volume, not a possible-image membership
theorem. B_I is a unit-ball integral structure; the source does not assert that
B_I (or a hull region containing it) is an actual archimedean possible image.
The inclusion B_I subset pi^{j+1}B_I is a container containment, not
B_I subset H_C,inf.

Conditional monotonicity: if B_I subset H_C,inf, then

    h_inf>=logvol(B_I)=0>=-S3,

and with actual B=I/R_B subset H_C,

    h_C>=H_B+h_inf>=H_B=(9/41)logp>Q_p,

so b=3 B=I P6 follows without needing h_inf>=-S3. But B_I subset H_C,inf and
h_inf>=0 are NOT source theorems.

Exact missing arch inputs:
  (A) B_I (or a hull region containing B_I) is an actual arch possible image;
  (B) a direct source lower bound h_inf>=0;
  (C) an actual H_C,inf computation containing the reference ball.

No arbitrary r_v/angular term is introduced. No counterexample
B_I not subset H_C,inf is constructed; the actual arch hull is missing.

## 4. Master case table

Let G-B = actual B=I/kappa+TC-B/R_B, G-ARCH = B_I subset H_C,inf (stronger
than G-HINF = h_inf>=-S3), E1 = no admissible complete b=273 C.

| case | branch assumption | arch input | b=3 P6 | b=273 |
|---|---|---|---|---|
| I | both branches possible (FALSE/NOT SOURCE) | B_I in H_C,inf | would hold | needs E1 |
| II | actual B=I (G-B) + R_B subset H_C | B_I in H_C,inf | P6 | E1 |
| III | actual B=I (G-B) + R_B subset H_C | h_inf>=-S3 | P6 | E1 |
| IV | actual B=I (G-B) + R_B subset H_C | neither | open | E1 |
| V | actual B=O_K | any IV arch | not from R_B; needs h_inf>=D3>A impossible under IV | E1 |
| VI | actual B=O_K or B=I, no E1 | any | b3 conditional | counterexample/unknown |

Case I is the hypothetical shortcut; task-362 shows it is FALSE as a source
statement. It cannot be used. Cases II/III are the legitimate conditional
P6-true corridors. Case V shows the B=O_K branch cannot be rescued by the IV
arch bound. Case VI is the open counterexample/E1 branch.

## 5. Conditional P6-true theorem

Theorem 5.1. Assume:

  (E1) no admissible complete C with the fixed F_mod=Q uniform b=273 profile;
  (G-B) the actual branch for the fixed b=3 C is B=I, equivalently
        kappa in [1,40], with TC-B and R_B subset H_C;
  (G-ARCH) either B_I subset H_C,inf or h_inf>=-S3.

Then b=3 B=I satisfies P6; b=273 is excluded by E1. More explicitly:

  - If G-ARCH = B_I subset H_C,inf: h_inf>=0 and
    h_C>=H_B+h_inf>=H_B>Q_p, so P6.
  - If G-ARCH = h_inf>=-S3: h_C>=H_B+h_inf and
    F<=-S3-h_inf<=0, so P6.

Proof. Actual B=I/TC-B gives R_B subset H_C and h_C>=H_B+h_inf. The arch input
gives h_inf>=0 or h_inf>=-S3. Compare with Q_p. QED.

This is conditional: E1, G-B, and G-ARCH are unproved. It is not a P6 proof
independent of the actual branch: if the actual branch is B=O_K, R_B is not an
actual possible-image family and the H_B lower bound is unavailable.

## 6. Reconcile E1 and b=3 routes

E1: no admissible complete C with the uniform b=273 profile. It is not proved;
prior Def3.1/q-order/BPS/Theta attacks found no arithmetic contradiction, only
missing complete C/BPS/Theta data. E1 is not E2 (E2 is CFTH/TC/arch failure).

Reconciliation:

  - E1 removes the b=273 profile. It does not help the b=3 route except by
    eliminating the competing positive-D profile; the b=3 route still needs
    actual B=I + R_B + arch input.
  - If E1 is false and a b=273 complete C exists, the b=273 lower/JP-G1
    machinery may give a P6 counterexample (conditional on JP+G1) or leave P6
    open; P6-true is not established. E1 is the exact b=273 exclusion needed
    for P6-true.
  - The branch audit forbids using both branches to make R_B unconditional;
    so the b=3 P6 corridor is tied to actual B=I, not to E1.
  - The arch audit forbids using B_I-zero/normalization as h_inf>=0; the
    arch input remains a separate missing theorem (B_I inclusion or h_inf>=-S3).

## 7. Exact gap list

P6-true v6 conditional inputs:

  1. E1: no admissible b=273 complete C. NOT PROVED.
  2. G-B: actual B=I/kappa in [1,40], with TC-B/R_B subset H_C. NOT PROVED
     (kappa underdetermined; task-269; branch audit task-362).
  3. G-ARCH: B_I subset H_C,inf (strong) or h_inf>=-S3. NOT PROVED; IV gives
     only the upper container H_C,inf subset pi^{j+1}B_I and h_inf<=A_proc;
     B_I-zero is normalization, not membership.
  4. Actual complete uniform C/TC/arch/BPS/Theta; exact H_C,inf.
  5. Scope: other b profiles not covered by E1/b=3; full P6 needs them handled.
  6. JP/G1: not P6-true inputs; they are conditional b=273 counterexample
     machinery. If E1 is false and JP+G1 hold, P6 is false; if E1 true, the
     JP+G1 b=273 counterexample is vacuous. JP is not a source theorem; G1
     unproved.

No mixed/E3 is used. No arbitrary r_v/point/branch union.

## 8. Next theorem

Single next theorem for P6-true v6: G-B, the actual B=I/kappa realization.

Target G-B: prove that the actual fixed b=3 C has B=I, equivalently

    kappa=e*vp(Tr y1)-vpi(y1) in [1,40],

with the L_B row family and TC-B/R_B subset H_C. This is the branch audit's
exact missing input: without it R_B is not an actual possible-image family and
the H_B lower bound is unavailable.

Why G-B first:

  - Branch audit (task-362) removes the both-branch shortcut; actual B=I is
    now load-bearing for every P6-true b=3 corridor.
  - If G-B is proved, the b=3 route reduces to the arch input G-ARCH; if the
    actual branch is B=O_K, the P6-true b=3 route is unavailable and the arch
    requirement D3>A is impossible under IV.
  - G-ARCH is the immediate second theorem: prove B_I subset H_C,inf (then
    h_inf>=0, strongest) or h_inf>=-S3. E1 remains the independent b=273
    exclusion.

If G-B is false (actual B=O_K or kappa>=41), P6-true b=3 via R_B fails; then
the branch is B=O_K with h_inf<=A_proc<D3, giving only the upper-bound
F<=D3-h_inf and no P6 proof. The only remaining P6-true route would require a
different arch/finite mechanism, not the B=I corridor.

## 9. Inconsistency/concept flags

  - H_C is the hull of the actual source possible images, not of both abstract
    B branches; "both branches possible" is FALSE/NOT STATED (task-362).
  - R_B subset H_C is conditional on actual B=I/TC-B, not independent of kappa.
  - B_I subset H_C,inf is NOT proved; IV gives the opposite container
    H_C,inf subset pi^{j+1}B_I. B_I-zero is normalization, not membership.
  - h_inf>=0 is conditional on B_I inclusion; h_inf>=-S3 is a separate open
    arch bound (task-349/361).
  - B_I arch unit ball is not the B=I finite row lattice; the arch and finite
    B=I objects are different.
  - E1 is not E2; E1 unproved.
  - JP/G1 are conditional b=273 counterexample machinery, not P6-true inputs.
  - No mixed/E3; no arbitrary branch union or r_v.
  - E48 sign; C1 lower=>F upper.
  - H=GL2/mod41/F_sem results are independent of P6.

## 10. Dependency references

    C9-POSSIBLE-BRANCH-AUDIT-20261025.md (task-362; branch actual only)
    C9-ARCH-BI-POSSIBLE-20261025.md (task-363; B_I arch not source)
    C9-P6TRUE-MASTER-20261025.md (task-351; prior master)
    C9-P6TRUE-ARCH-S3-20261025.md (task-349; h_inf>=-S3 obstruction)
    C9-ARCH-S3-JP-20261025.md (task-361; arch gap O1-O5)
    C9-JP-REPAIR-20261025.md (task-341; JP/G1 conditional)
    C9-B3-P6-ASSEMBLY-20261025.md (H1-H4 assembly)
    C9-BI-REGION-HULL-20261025.md (R_B conditional)
    C9-KAPPA-ACTUAL-20261025.md (G-B obstruction)

Status: P6-true v6 conditional on E1+G-B+G-ARCH; both-branch shortcut false;
B_I arch inclusion unproved; actual B=I/kappa missing; h_inf>=-S3 missing; E1
missing. No unconditional P6. No mixed/E3; no Lean/Project edits;
target_accepted=false.

## 11. Acceptance

Only C9-P6TRUE-MASTER-V6-20261025.md written. Natural-language master/audit
synthesis only; no Lean/Project/target edits; no independent review/kernel/
comparator run. target_accepted=false; complete C9/P6 not proved.
