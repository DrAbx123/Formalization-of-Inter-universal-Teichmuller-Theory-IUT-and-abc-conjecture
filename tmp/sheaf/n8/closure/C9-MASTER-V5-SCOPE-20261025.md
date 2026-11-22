# C9 master v5 scope correction: mixed profiles are E3, uniform-only chain

Task: task-318. Owner: multiradial. Date: 2026-10-25.
Stage: SHEAF stage1 natural-language theorem/scope correction only. No Lean/
Project edits. No new arbitrary assumptions. Deliverable: this file only.
target_accepted=false; P6 open.

## 0. Scope correction and verdict

TAME Section 5 mixed bad/good profiles are a DIFFERENT profile and are NOT
possible images of the fixed F_mod=Q uniform target.

Exact source reasons:

  - IUT I Definition 3.1(e): V is a section V(F_mod)->V; for F_mod=Q each
    rational prime p has ONE selected place. The fixed uniform target uses the
    selected all-bad place, bad mass rho=1.
  - Bad mass for the fixed uniform profile is rho in {0,1}; it is not a
    continuously variable parameter.
  - C9-GLOBAL Section 1 explicitly forbids replacing unselected conjugate
    places by a new rho=1/2 average to avoid the uniform case.
  - A mixed bad/good tuple requiring good factors at the same p is a different
    E3 profile, with different normalized weights/target column. It is not an
    additional possible image inside the fixed uniform C.

Consequence: the mixed-profile results of tasks 303/304/305/310/311/313 are
profile-change/E3 results. They cannot be used for the original P6 uniform
target. In particular:

  - no mixed P6 rescue for positive-D b=3/b=273;
  - no mixed counterexample or mixed U/NPC refutation;
  - no mixed-profile "positive target complement" for the fixed uniform C;
  - all mixed v4 sections claiming U false, mixed rescue, or mixed
    counterexample are RETRACTED by this v5 scope correction.

Task-307 confirms: the mixed region is actual for the mixed profile, but NOT a
possible image of the fixed uniform F_mod=Q C. The task-299 mixed-profile
challenge is therefore E3, not an NPC countermodel.

Uniform-only master chain:

  (1) b=3 B=I conditional P6: actual B=I + TC-B/R_B subset H_C +
      h_C>=h_B+h_inf + h_inf>=-S_3 => b=3 P6.
  (2) b=3 B=O_K: C1 gives only F<=D_3-h_inf; no P6 proof and no counterexample.
  (3) b=273: C1 gives only F<=D_A/B-h_inf; no P6 proof and no counterexample;
      b=273 no-go invalid.
  (4) R_A subset R_B is PROVED (row-hull inclusion); SAT-U/NPC is NOT proved.
      Conditional on U/NPC, b=273 gives F>=8821.538891>0 and b=3 has the
      h_inf split; without U/NPC, both remain open.
  (5) BPS root ambiguity is relative/absorbed; absolute root and global
      BPS/Theta-pilot 0-column remain missing.
  (6) No unconditional P6 proof and no unconditional counterexample.

The next decisive uniform-profile theorem is NPC/M3 (equivalently U):
for the fixed uniform target, H_C has no positive-volume complement beyond
R_B+arch, hence h_C<=H_B+h_inf. This is the missing upper side; mixed profiles
cannot supply or refute it.

## 1. Scope obstruction: why mixed is E3

Theorem 1.1 (mixed not in fixed uniform target). For a fixed complete C with
F_mod=Q and the uniform all-bad profile at the selected place p over p=12301,
the TAME Section 5 mixed bad/good region is not an element/possible image of the
target possible-image family H_C.

Proof. I Def3.1(e) gives a section V(F_mod)->V; F_mod=Q has one selected place
for each rational p. The fixed uniform target at p selects the all-bad local
type with rho=1. TAME Section 5 mixed profile requires a tuple with good factors
at p (0<rho<1) and a different normalized q/weight/Theta column. C9-GLOBAL
Section 1 rules out replacing unselected conjugates by an averaged rho=1/2
profile. Hence the mixed region is not in H_C; it is an E3 profile change. QED.

Corollary 1.2. The mixed-profile formulas/results are valid only for the E3
mixed-profile object. They do not establish:

  - a lower bound h_C>=H_mixed+h_inf for the fixed uniform C;
  - an upper-bound refutation U_false for the fixed uniform C;
  - an NPC countermodel for the fixed uniform C;
  - any P6 rescue or P6 counterexample for the fixed uniform C.

The mixed hash/result list is marked E3-EXCLUDED in Section 12.

## 2. Sign and uniform local arithmetic

p=12301, e=41, uniform profile, F(C):=Q_C-h_C.

    P6 target: h_C>=Q_C  <=>  F(C)<=0.                            (2.1)
    F>0: counterexample; F<0: P6 holds; F=0: boundary.

b=3:

    Q_p=(-3/41)log p,
    H_A=(-411/41)log p, D_3=Q_p-H_A=(408/41)log p=93.7149712746...,
    H_B=(9/41)log p,    S_3=H_B-Q_p=(12/41)log p=2.7563226845...,
    H_B-H_A=(420/41)log p=96.471293959....

b=273:

    Q_p=(-273/41)log p,
    H_A=(-39156/41)log p, D_A=(38883/41)log p=8931.174578603...,
    H_B=(-38736/41)log p, D_B=(38463/41)log p=8834.703284644....

Arch B_I-zero: h_inf<=A_proc=11.5 log pi=13.164393687... (upper only).

C1/C3 direction:

    h_C >= sum_p alpha_p H_p^Sp log p + h_inf,                     (C1)
    F=Q_C-h_C <= D_C^Sp-h_inf.                                    (C3)
C1 is lower on h_C; C3 is upper on F. Positive upper does not prove F>0.
E48 remains binding.

## 3. Theorem 1: b=3 B=I conditional P6 (uniform)

Theorem 3.1. Let C be a complete admissible C with the fixed uniform b=3
profile. Assume:

  (H1) actual B=I branch at p;
  (H2) TC-B/full possible-image hull: R_B subset H_C;
  (H3) h_C>=h_B+h_inf, h_B=(9/41)log p;
  (H4) h_inf>=-S_3=-(12/41)log p.

Then F=Q_C-h_C<=-S_3-h_inf<=0, so h_C>=Q_C and b=3 P6 holds for C.

Proof. h_C>=h_B+h_inf; H4 gives -S_3-h_inf<=0; subtract Q_p. QED.

Conditional only: H1-H3 missing/conditional, H4 unproved. No mixed profile is
used.

## 4. Theorem 2: b=3 B=O_K only upper

Theorem 4.1. Under C1 with h_C>=H_A+h_inf:

    F<=D_3-h_inf=(408/41)log p-h_inf.
    If h_inf<=A_proc, the right side is at least 80.550578, not bounded above
    by 80.550578.                                                (4.1)

This is a positive UPPER bound on F; no P6 proof and no counterexample. Mixed
profiles are excluded and cannot supply a lower-bound rescue for the fixed
uniform target.

## 5. Theorem 3: b=273 only upper, U conditional

Theorem 5.1. Under C1:

    B=O_K: F<=D_A-h_inf=(38883/41)log p-h_inf;
    B=I:   F<=D_B-h_inf=(38463/41)log p-h_inf.
For h_inf<=A_proc the right sides are at least 8918.010 and 8821.539, positive.
They are upper bounds on F; no P6 proof and no counterexample.

Conditional saturation upper U273:
    h_C<=H_B+h_inf.
If U273 holds, F>=D_B-A_proc=8821.538891>0, so b=273 is a conditional P6
counterexample in both B branches. U273 is NOT proved; it is exactly the missing
NPC/M3 target-exhaustion theorem. Mixed profiles do not refute U273 for the
fixed uniform target (they are E3 and excluded).

## 6. Theorem 4: row inclusion R_A subset R_B

Theorem 6.1. With TAME row lattices

    L_A=sum_i p^s pi_i D_r (B=O_K),  L_B=p^{s-r+1}J^{tensor r} (B=I),
    J=pi O_K, D_r=O_K^{tensor r},

L_A subset L_B; r=1 equality, r>=2 strict. Hence R_A subset R_B.

Proof. For each L_A generator e_i=p^s pi_i, multiply the B=I generator
b=p^{s-r+1}pi_1...pi_r by prod_{j!=i}(p/pi_j) in D_r:
  b*prod_{j!=i}(p/pi_j)=p^{s-r+1}pi_i p^{r-1}=p^s pi_i=e_i.
p/pi_j=pi_j^{e-1}u_j^{-1} in O_{K_j}, so the multiplier is integral; all e_i in
L_B; L_A subset L_B. Strictness r>=2 from pi-content. QED.
Normalized height gap nu_B-nu_A=(r-1)(1-1/e)logp>0.
This proves S1 only, not target-upper H_C subset Hull(L_B).

## 7. Theorem 5: SAT-U/NPC exact status

Definitions:
    U: h_C<=max(H_A,H_B)+h_inf=H_B+h_inf.
    NPC/M3: for the fixed uniform target, H_C has no positive-volume complement
    beyond R_B+arch; equivalently U.

Status:

  - U is NOT proved. TAME Section 6 gives local row saturation for the fixed
    all-bad subfamily, not global target exhaustion.
  - NPC/M3 is NOT proved and NOT refuted for the fixed uniform target.
  - TC-B is a lower/saturation inclusion (source regions inside H_C), not an
    upper H_C subset R_B+arch.
  - R_A subset R_B is proved, but H_C may contain other target possible-image
    classes (good/arch/aggregate/other local/BPS-Theta) not bounded by row hulls.
  - task-301 abstract extra-region model is TC-valid but not source-valid;
    task-302 conditional S2 only; task-300 conditional U.
  - task-299's mixed-profile challenge is E3, so it does NOT refute NPC/U for
    the fixed uniform target.
  - The mixed-profile "U false" claim in C9-MASTER-V4 is RETRACTED.

Conditional consequences if NPC/U is supplied:

    U273 => h_C<=H_B+h_inf<=H_B+A_proc=-8884.245232...<Q_p=-62.706341...,
             F>=D_B-A_proc=8821.538891>0 (b=273 counterexample both branches);
    U3  => b=3 split: h_inf<-S_3 counterexample; h_inf=-S_3 boundary;
             h_inf>-S_3 P6 with B=I region lower, otherwise undetermined.

No mixed profile enters these implications.

## 8. Theorem 6: BPS root relative/absorbed, global BPS missing

For E546, q=p^546u_q. Once a uniformizer pi of K_v is fixed, q/pi^22386=v^82
with v in 1+pZ_p unique (82 invertible on 1+pZ_p), and
  qhat_pi=pi^273v, qhat_pi^82=q, vpi(qhat_pi)=273/41, order b=273.
This is a relative canonical 82nd root. There is NO absolute canonical root:
roots form a mu_82-torsor, 82|p-1, and pi is not fixed by E546.

Root rotation a->zeta a (zeta in mu_82) is absorbed by
zeta_j->zeta^{-j^2}zeta_j:
  g'_j=zeta^{-j^2}zeta_j(zeta a)^{j^2}=zeta_j a^{j^2}=g_j.
Thus Gaussian monoid, Kummer classes, Theta/Gaussian values, zero-label
splitting and q/b=273 target column are invariant. The ambiguity is auxiliary,
not a genuinely different BPS value profile. Task-294/296 correct the earlier
task-292 reading of two different BPS profiles.

Global BPS is still not constructed: mono-theta environments, theta/Gaussian
monoids, evaluation points, Kummer classes, symmetrizing/gluing, Theta-pilot
0-column and target data remain missing (O1-O4). Relative root does not give an
absolute root or global BPS label.

## 9. Retraction record: mixed profiles and V4

RETRACTED for the original uniform P6:

  - C9-MASTER-V4-20261025.md sections claiming:
      * mixed profiles make U false;
      * mixed profiles give a P6 rescue for positive-D b=3/b=273;
      * mixed profiles give a counterexample or NPC countermodel;
      * U is closed negative by mixed profiles.
    These are E3 profile-change claims; V4 is superseded by this V5 for scope.
    V4's uniform-only formulas/chain remain, but the mixed sections must not be
    cited for original P6.
  - task-303/304/305/310/311/313 mixed-profile results: valid only for the E3
    mixed profile, NOT usable for fixed F_mod=Q uniform P6. In particular:
      * task-303 fixed-Q mixed rescue conclusion is not applicable to the
        uniform target;
      * task-304 profile-scaled mixed threshold is an E3 result, not uniform;
      * task-305 "U false by mixed" is E3, not a uniform refutation.
  - task-299 "target hull contains mixed region" is E3 for the fixed uniform C;
    task-307 confirms the scope failure.

NOT retracted: the mixed-profile formulas are mathematically valid for their
own E3 profile; they are simply not the original target. No claim is made that
mixed E3 statements are false.

## 10. Master status and exact obstruction

Theorem 10.1 (v5 master). Exact status:

  (i) P6 <=> F=Q_C-h_C<=0; C1 gives only F<=D_C^Sp-h_inf.
  (ii) b=3 B=I: conditional P6 under H1-H4; not actual.
  (iii) b=3 B=O_K: only F<=D_3-h_inf; no P6 proof/counterexample.
  (iv) b=273: only F<=D_A/B-h_inf; no P6 proof/counterexample. U/NPC conditional
       counterexample; U not proved.
  (v) R_A subset R_B proved (S1); target generation by two B rows false (S2);
      NPC/M3 missing.
  (vi) Mixed profiles are E3 and excluded; no mixed P6 rescue/counterexample/U
      refutation for the original uniform target.
  (vii) BPS root relative/absorbed; absolute root/global BPS missing.
  (viii) No unconditional P6 proof and no unconditional counterexample.

Exact missing uniform inputs:

  1. actual B=I branch/kappa or actual B=OK branch with a different P6 route;
  2. actual TC-B/full possible-image hull H_C and R_B transport;
  3. actual h_inf and h_inf>=-S_3;
  4. actual complete C/S_bad/weights/fixed q class;
  5. NPC/M3 target-exhaustion, equivalently U h_C<=H_B+h_inf;
  6. global BPS/Theta/0-column/gluing;
  7. b=273 exclusion or a genuine upper bound if NPC fails;
  8. for a counterexample, h_C<=Q_C-eps or TC equality.

## 11. Next uniform-profile theorem

Target theorem T_NPC (uniform target exhaustion / U). For the fixed F_mod=Q
uniform target:

    (NPC/M3) H_C has no positive-volume complement beyond R_B+arch;
    equivalently (U) h_C<=H_B+h_inf.

A proof should combine:

  (N1) TAME Section 6 local row saturation: each fixed all-bad row image lies in
       the B=O_K/B=I hull (inferred source consequence, conditional);
  (N2) R_A subset R_B (proved task-291/298);
  (N3) no other source target class in the fixed uniform profile adds positive
       volume outside R_B+arch: good finite h=0; arch is h_inf; aggregate/other
       local types BPS/Theta/Ind1 transport the same rows or are nonpositive;
  (N4) hull-of-union/exhaustion: no additional possible-image class beyond the
       row+arch envelope (the exact missing NPC theorem).

Why this is the single most promising next uniform theorem:

  - It is the only missing upper side. If proved, U273 gives the b=273
    conditional counterexample F>=8821.538891>0 in both B branches, and U3 gives
    the exact b=3 h_inf split.
  - R_A subset R_B is already proved, removing S1. TAME local saturation gives
    N1 conditionally. The remaining gap is precisely N3/N4, a uniform-profile
    target-exhaustion statement.
  - Mixed-profile objections are E3 and excluded; they neither prove nor refute
    NPC/U for the fixed uniform target.
  - It does not require constructing a canonical absolute BPS root: the relative
    root is available and root ambiguity is absorbed; BPS/Theta labels are
    needed only for the target-exhaustion bookkeeping.

Second priority remains T_B (actual B=I/kappa) for the b=3 B=I corridor and
T_arch (h_inf>=-S_3); but T_NPC is the decisive upper-side theorem.

## 12. Inconsistency / concept flags

  - Mixed TAME Section 5 is E3 profile change; fixed F_mod=Q V-section selects
    one place/rational p and uniform rho=1. Do not insert mixed regions.
  - U is NOT false; mixed E3 does not refute it. U/NPC remains unproved.
  - No mixed P6 rescue or mixed counterexample for original P6.
  - V4 mixed sections are retracted by this V5; history retained.
  - R_A subset R_B does not imply H_C subset Hull(L_B); S2/NPC still needed.
  - BPS root rotation is absorbed; global BPS/Theta 0-column missing.
  - C1 lower => F upper; E48 sign correction.
  - b=273 no-go invalid; U/NPC conditional b=273 counterexample only.
  - h_inf<=A_proc is upper only.
  - H=GL2/F_sem degree facts are independent of P6.

## 13. Dependency hashes

Uniform results:

    C9-MASTER-V3-20261025.md                    3E6E9595... (335)
    C9-REGION-INCLUSION-20261025.md              CAB842ED... (140)
    C9-RA-SUBSET-RB-20261025.md                  B89DC64C... (147)
    C9-TARGET-GENERATED-20261025.md              F5139CDB... (132)
    C9-B3-SATURATION-20261025.md                 B32A524B... (143)
    C9-SATURATION-MAXIMALITY-20261025.md         DAA9CD08... (108)
    C9-TARGET-UPPER-SAT-20261025.md              AFB86168... (112)
    C9-S2-UPPER-INDEPENDENT-20261025.md          33FC2C9F... (136)
    C9-THETA-ROOT-CANONICAL-20261025.md          42C1CAB0... (104)
    C9-B273-BPS-CONSTRUCTION-20261025.md          D572D9C3... (85)
    C9-BPS-AMBIGUITY-AUDIT-20261025.md            8AF187B6... (183)
    C9-NPC-M3-20261025.md                         4E519EDE... (112)
    C9-MASTER-V4-20261025.md                      E89D1344... (356; mixed
                                                  sections RETRACTED, uniform
                                                  parts superseded by V5)

E3-EXCLUDED (mixed-profile; not original P6):

    C9-MIXED-PROFILE-P6-20261025.md               3FE77524... (181)
    C9-MIXED-VOLUME-EXACT-20261025.md             0B5149C0... (212)
    C9-MIXED-UPPER-20261025.md                    69868BFB... (142)

Status: uniform-only chain restored; b=3 B=I conditional P6; b=3 B=OK and
b=273 only upper/open; R_A subset R_B proved; U/NPC missing; mixed E3 excluded;
BPS root relative/absorbed, global BPS missing. Next uniform theorem T_NPC
(target exhaustion/U); T_B/T_arch second. P6 open; no unconditional proof/
counterexample. No Lean/Project edits; target_accepted=false.

## 14. Acceptance

Only C9-MASTER-V5-SCOPE-20261025.md written. Natural-language theorem/scope
correction only; no Lean/Project/target edits; no independent review/kernel/
comparator run. target_accepted=false; complete C9/P6 not proved.
