# C9 P6-true master: E1 b=273 exclusion + b=3 route

Task: task-351. Owner: multiradial. Date: 2026-10-25.
Natural-language master strategy only. No Lean/Project edits. No new arbitrary
assumptions; no mixed/E3 profile. Deliverable: this file only.
target_accepted=false; P6 open.

## 0. Purpose and verdict

This is the P6-TRUE master: exclude the b=273 profile via E1, then prove b=3 P6
through the B=I region and the arch lower bound:

    E1: no admissible complete C with the fixed F_mod=Q uniform b=273 profile;
    b=3: actual B=I/kappa + R_B subset H_C + h_C>=h_B+h_inf + h_inf>=-S_3
         => h_C>=Q_p and b=3 P6 holds.

Both E1 and the b=3 hypotheses are UNPROVED. The conditional master is:

    E1 + b=3 route => P6 true on the b=3/b=273 critical profile class,
    provided the b=3 hypotheses hold for every admissible b=3 C.

It is not a full unconditional P6 proof: E1 is open, H1-H4 are open, and other
b profiles are not covered by E1 or by the b=3 theorem. No mixed/E3 region is
used.

Reconciliation with JP/G1: JP+G1 (if valid) would make b=273 a conditional P6
counterexample F>=8821.538891 when a b=273 complete C exists. E1 says no such C
exists. Thus E1 and JP+G1 are compatible: under E1 the JP+G1 b=273
counterexample is vacuous. If E1 is false and JP+G1 hold, P6 is false, not true.
E1 is therefore the branch selector for the P6-true strategy; JP/G1 do not
support P6-true without E1.

## 1. Sign and local arithmetic

p=12301, e=41, fixed F_mod=Q uniform profile, F(C)=Q_C-h_C.

    P6 target: h_C>=Q_C  <=>  F(C)<=0.                            (1.1)
    F>0: P6 counterexample; F<0: P6 holds; F=0: boundary.

b=3:

    Q_p=(-3/41)log p,
    H_A=(-411/41)log p, H_B=(9/41)log p,
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

## 2. E1: b=273 exclusion

Definition E1. There is no admissible complete C with the fixed F_mod=Q
uniform b=273 profile at the selected bad place p over p=12301; equivalently
the b=273 uniform profile is outside the admissible complete-C class.

Status: E1 is NOT proved. Prior attacks (Def3.1, q-order, BPS/Theta, complete
C construction) did not produce an arithmetic contradiction; the b=273 E_546
skeleton is admissible at the skeleton level but not a complete C. E1 is a
structural exclusion of the full complete C/BPS/Theta/target object, not a
local b=273 defect. It is also not E2: E2 is the failure of CFTH/TC/arch on an
admissible C; E1 is nonexistence of such a C.

Consequences:

  - If E1 holds: no b=273 complete C exists; the JP+G1 b=273 conditional
    counterexample is vacuous; b=273 cannot refute P6.
  - If E1 fails and JP+G1 hold: a b=273 complete C exists and JP+G1 give
    F>=D_B-A_proc=8821.538891>0; P6 is FALSE for that C. P6-true fails.
  - If E1 fails but JP/G1 are not proved: b=273 remains an open obstruction;
    P6-true is not established, but no counterexample is proved either.

Thus E1 is the first load-bearing theorem of the P6-true strategy, and the
b=273 counterexample direction is its exact alternative.

## 3. b=3 route

Theorem 3.1 (conditional b=3 P6). Let C be a complete admissible C with the
fixed F_mod=Q uniform b=3 profile. Assume:

  (H1) actual B=I branch at p (equivalently kappa=e*vp(Tr y1)-vpi(y1) in
       [1,40] for the actual Kondo y1);
  (H2) R_B subset H_C: the B=I sibling region is contained in the target
       holomorphic hull (TC-B/full possible-image hull);
  (H3) h_C>=h_B+h_inf with h_B=(9/41)log p (the R_B sibling volume plus arch
       is a lower bound for the target hull);
  (H4) h_inf>=-S_3=-(12/41)log p.

Then

    h_C >= h_B+h_inf = (9/41)log p+h_inf >= (9/41-12/41)log p
         = (-3/41)log p = Q_p,
    F=Q_C-h_C <= Q_p-h_B-h_inf = -S_3-h_inf <= 0,

so h_C>=Q_C and b=3 P6 holds for C.

Proof. H3 and H4; subtract Q_p. QED.

H1-H4 status:

  - H1 is the actual B branch/kappa theorem; not proved. The only viable b=3
    P6 route uses B=I; if kappa<=0 then B=O_K and this route does not apply.
  - H2 is conditional on TC-B/full possible-image hull and the sibling region
    R_B (tasks 272/274); not an actual complete C.
  - H3 is the R_B volume lower bound h_B; conditional on H1/H2 and the B=I
    sibling construction.
  - H4 h_inf>=-S_3 is unproved: B_I-zero/IV gives only the upper bound
    h_inf<=A_proc; task-270/278/283 exact obstruction, no arch lower bound.
  - Actual complete C/TC/arch/BPS/Theta data are missing.

No mixed/E3 profile enters H1-H4.

## 4. Conditional P6-true master

Theorem 4.1 (conditional P6-true on the critical class). Assume:

  (E1) no admissible complete C with the b=273 uniform profile;
  (B3) Theorem 3.1 hypotheses H1-H4 hold for every admissible b=3 uniform C.

Then for every admissible complete C whose uniform profile is b=3 or b=273,
P6 holds:

  - b=273: no such C by E1 (vacuous);
  - b=3: Theorem 3.1 gives h_C>=Q_C.

Proof. Immediate from E1 and Theorem 3.1. QED.

Scope limitation (exact): E1 excludes only the b=273 profile, and Theorem 3.1
handles only b=3. Other positive-D b values (e.g. b=1347 and other uniform
b>=5) are not excluded by E1 and not handled by the b=3 theorem. Therefore
Theorem 4.1 is a P6-true master for the b=3/b=273 critical profile class, not
an unconditional P6 proof for all profiles. A full P6-true proof needs either
E1 generalized to all b!=3 or a separate P6 theorem for every other b; that is
the remaining scope gap.

## 5. Reconciliation with JP/G1 and b=273 counterexample

JP: every D^dag-prime-strip isomorphism in full Ind1 acts on J=pi O_K by an
Aut_Zp(J) lattice automorphism, so L_B=p^{s-r+1}J^{tensor r} is invariant.
JP is NOT a source theorem from IUT I Def4.1/Def4.10/Prop4.11 alone (task-333:
D-prime-strips are categories up to equivalence; an isomorphism induces an
outer G_K automorphism, not a chosen J action). H_A-lite covers only the
symplectic subgroup H, not full Ind1; H_A-full open.

G1: every finite possible image of the fixed uniform target is a row image
(L_A/L_B), so TAME §6 row classification is an upper bound for the full target
finite family. G1 is NOT proved: TAME §6 is local/all-bad subfamily only and
explicitly disclaims a whole-C upper bound; good/arch/other branches and full
Ind1/Ind2/Ind3/BPS/Theta remain.

Conditional NPC/U: JP+G1 => L_B invariant and every finite possible image in
R_B; hence U h_C<=H_B+h_inf. For b=273, U gives

    h_C<=H_B+h_inf<=H_B+A_proc=-8884.245232...<Q_p,
    F>=D_B-A_proc=8821.538890956...>0.

Reconciliation:

  - If E1 holds, no b=273 complete C exists, so the JP+G1 b=273 counterexample
    is vacuous. No contradiction: E1 selects the no-b=273 branch.
  - If E1 fails and a b=273 complete C exists, JP+G1 make P6 false for that C;
    then P6-true is impossible. JP/G1 therefore strengthen the counterexample
    alternative, not the P6-true conclusion.
  - If E1 fails but JP or G1 fails, b=273 remains open; P6-true is neither
    proved nor refuted.
  - The b=3 route Theorem 3.1 does not require JP/G1: it is a lower-bound
    argument using R_B subset H_C and h_inf>=-S_3. JP/G1 concern the upper
    side; they do not replace H1-H4.

Thus the master is consistent: P6-true needs E1 (to remove b=273) plus the b=3
lower route. JP/G1 are a separate conditional counterexample branch that E1
must exclude; if E1 is false and JP/G1 hold, the answer is P6-false, not
P6-true.

## 6. Exact hypotheses and obstruction list

P6-true conditional inputs:

  1. E1: no admissible complete C with the b=273 uniform profile. NOT PROVED;
     prior Def3.1/q-order/BPS/Theta attacks found no arithmetic contradiction,
     only missing complete C/BPS/Theta data.
  2. b=3 H1: actual B=I/kappa in [1,40]. NOT PROVED; kappa underdetermined
     (task-269), JW relations attack task-282/344.
  3. b=3 H2: R_B subset H_C for the fixed uniform target. Conditional on TC-B
     and the B=I sibling; actual complete C/TC-B missing.
  4. b=3 H3: h_C>=h_B+h_inf. Conditional on H1/H2/R_B volume.
  5. b=3 H4: h_inf>=-S_3. NOT PROVED; arch lower bound exact obstruction.
  6. b=3 actual complete C/TC/arch/BPS/Theta.
  7. Scope: all other b profiles; E1 is b=273 only.

No new arbitrary assumption substitutes for 1-7. No mixed/E3.

## 7. Next theorem

Single next theorem for the P6-true master: E1.

    E1: no admissible complete C realizes the fixed F_mod=Q uniform b=273
        profile.

Why E1 is the next theorem:

  - It is the first load-bearing input of Theorem 4.1 and the exact branch
    selector against the JP/G1 b=273 counterexample. Without E1, the best P6
    result is conditional/open and a b=273 complete C plus JP+G1 would make P6
    false.
  - It is a precise structural statement about the full complete C, not an
    arithmetic local defect; prior work has not proved it, but it is the
    decisive missing statement for P6-true.
  - The b=3 H1-H4 route is independent and remains the second front; if E1 is
    proved, the next theorem is actual B=I/kappa + h_inf>=-S_3 (tasks 344/349),
    then R_B subset H_C (task 350).

Alternative if E1 is false: construct an admissible b=273 complete C and prove
JP+G1. That would make b=273 a P6 counterexample F>=8821.538891 and establish
P6-false, not P6-true. This is the exact dichotomy; no third option yields
P6-true.

If E1 is unprovable but no b=273 C is constructible, E1 remains an open
exclusion hypothesis; P6-true is not established.

## 8. Inconsistency / concept flags

  - E1 is not E2: E1 = no admissible b=273 C; E2 = CFTH/TC/arch failure on an
    admissible C.
  - E1 is not proved; the b=273 skeleton admissibility is only a skeleton.
  - JP is not a source theorem; G1 is not proved; JP+G1 only give a conditional
    b=273 counterexample. E1 makes it vacuous if true.
  - b=3 H1-H4 are conditional; no unconditional b=3 P6 proof.
  - E1/b=3 route covers only the b=3/b=273 critical class; other b profiles
    are a scope gap.
  - No mixed/E3 region enters.
  - C1 lower => F upper; E48 sign correction.
  - H=GL2/mod41/F_sem results are independent of P6.

## 9. Dependency references

    C9-B273-EXCLUSION-20261025.md and CORR2 (E1 attacks; E1 not proved)
    C9-B273-ADMISSIBILITY/COMPLETE-C (E1 structural obstruction)
    C9-B273-GLOBAL-BPS-20261025.md (global BPS obstruction)
    C9-IND1-J-ACTION-20261025.md (JP conditional)
    C9-NPC-VERIFY-INDEPENDENT-20261025.md (JP not source; G1)
    C9-IND1-KZERO-20261025.md (unit/log k=0 conditional)
    C9-B3-P6-ASSEMBLY-20261025.md (b=3 H1-H4 assembly)
    C9-ARCH-LOWER-S3-20261025.md (H4 obstruction)
    C9-BI-REGION-HULL-20261025.md (H2/H3 conditional)
    C9-KAPPA-ACTUAL-20261025.md (H1 obstruction)
    C9-NPC-NORMALIZATION-20261025.md (JP/G1 conditional; U caveat)
    C9-MASTER-V5-SCOPE-20261025.md (uniform-only scope)

Status: P6-true master conditional on E1 + b=3 H1-H4; E1 not proved; b=3 route
conditional; JP/G1 conditional counterexample branch compatible only if E1
false; other b profiles scope gap. No unconditional P6 proof, no Lean/Project
edits; target_accepted=false.

## 10. Acceptance

Only C9-P6TRUE-MASTER-20261025.md written. Natural-language master strategy/
theorem-obstruction only; no Lean/Project/target edits; no independent review/
kernel/comparator run. target_accepted=false; complete C9/P6 not proved.
