# C9 audit: corrected global assembly (task-173)

Task: task-173. Audit of C9-GLOBAL-ASSEMBLY-CORRECTED under CFTH/TC, B branches,
archimedean maximal-container bound, residual formula, labels and radii.
Date: 2026-10-25. Owner: kummer. Stage: natural-language audit only.
No Lean/Project edits. Only this file written. target_accepted=false.

Inputs (current bytes):

| file | lines | SHA256 |
|---|---:|---|
| C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md | 230 | 8e7ef66a737bbfe73ed13ea568875a4d1305f48d814de4b3773bebb3db2f3548 |
| C9-ERROR-LEDGER-20261025.md | 495 | 06f8e743c35d2212f81db34bcd8f17483054b1aa82297772b55cae65fcd313b6 |
| C9-ARCH-SHELL-ATTACK-20261025.md | 192 | dce3c07bb6739378cc34a0eb204cdffc4080553d151e9f1bdccec72e78a93163 |
| C9-IND1-GLOBAL-20261025.md | 532 | 94785726ee890f6bc672861c570238f040636a6273a7722b2621949c48af9ab8 |
| C9-MODP-BRANCH-PROOF-20261025.md | 257 | af543bbbc50e8ec8cf9909cd5675d830018254760abc66410c81501a7227eade |

Binding prior corrections: SYMPLECTIC-SOURCE (H=Phi^{-1}(Sp), no rho
homomorphism), IND1-GLOBAL (TAME (11)-(14) withdrawn; TC-A..TC-H/TC-S), ERROR-
LEDGER E8 and C9-RADIUS-CORRECTION (base p=12301), MODP-BRANCH-PROOF (full
barGamma branch undetermined).

Verdict classes: VALID, CONDITIONAL, INVALID, WITHDRAWN.

## 1. Executive verdict

1. The residual formula is algebraically correct:

   Q_C - h_C <= D_C^Sp - h_inf(C),
   D_C^Sp = sum_{p in S_bad} alpha_p d_p log p,
   d_p = b(e+1)/12 - (b-1)/e - T_p.

   It is CONDITIONAL on CFTH, which explicitly includes the corrected donor and
   TC-A..TC-H/TC-S. It is not an unconditional global inequality. No complete C
   satisfying CFTH is constructed in the frozen files.

2. No global closure is claimed by GLOBAL-ASSEMBLY-CORRECTED. It explicitly
   says the earlier unconditional closure is withdrawn and only C1/C3 plus the
   radius criterion C4/C7 survive. That status statement is correct.

3. B branches: the corrected global assembly labels b=3 and b=273 with the
   B=O_K branch under the natural trace alignment. This is valid only for the
   subgroup H=Phi^{-1}(Sp), not for the full actual finite image barGamma.
   MODP-BRANCH-PROOF and ERROR-LEDGER E3 state the full branch is UNDETERMINED:
   B=O_K requires every gamma in barGamma to fix l=O_K/J; B=I occurs if some
   actual gamma moves l, or if the basis alignment fails with v!=0. The
   corrected global file does not supply the full-barGamma condition, so its
   B=O_K finite residual labels are CONDITIONAL on an additional
   barGamma(l)=l hypothesis, not on natural alignment alone.

4. Archimedean radii: D1/D2 in corrected global still use base e=41:
   r_inf >= pi*41^{d_p}. This is INVALID. C7 itself states the correct formula
   r_inf >= pi*p^{d_p}; p=12301. Correct values:

   - b=3, d_p=408/41:
     log10(p^{d_p}) = 40.6998948963;
     log10(pi p^{d_p}) = 41.1970447690;
     r_inf >= pi*12301^{408/41} ~ 1.5741451259e41.
   - b=273, d_p=38883/41:
     log10(p^{d_p}) = 3878.7598364020;
     log10(pi p^{d_p}) = 3879.2569862747.
     The often-quoted "log10 ~3878.76" is log10(r/pi), not log10 r; the radius
     itself has log10 ~3879.257.

   The old figures 3.51816e16 and 1530.0 are withdrawn.

5. Arch maximal-container bound: ARCH-SHELL gives the donor-independent
   source-container bound

     h_inf(C) <= A_arc = ((l+5)/4) log pi,  l=41, A_arc ~ 13.164394.

   For the conditional uniform b=3 deficit (408/41) log p with p=12301 this is
   about 93.715 natural, already above A_arc; b=273 is much larger. Therefore
   archimedean-only compensation is impossible in these profiles even without
   r_v<=pi. This is a VALID conditional source-container comparison, but it is
   not used in GLOBAL-ASSEMBLY-CORRECTED; the latter gives the radius criterion
   C4/C6/C7 but does not record A_arc. This omission does not prove closure; it
   sharpens the archimedean gap.

6. Shell branch r_v<=pi is not a source theorem. The single-factor shell is
   I_v={|a|<=pi}, but the level-j Theta-pilot is a tensor packet with
   source container pi^{j+1}B_I. ARCH-SHELL correctly says r_v<=pi is an extra
   strong hypothesis, not IV Thm1.10(vii). GLOBAL-ASSEMBLY-CORRECTED already
   calls the shell branch "not proved"; that conditional status is correct, but
   any use of r<=pi to infer h_inf<=0 must carry the extra hypothesis.

## 2. Itemized audit

### 2.1 Residual formula and CFTH

| item | status | comment |
|---|---|---|
| C2 D_C^Sp = sum alpha_p d_p log p | VALID ALGEBRA conditionally | Correct definition. |
| C3 Q_C-h_C <= D_C^Sp-h_inf | VALID ALGEBRA under C1 | Correct sign: h_inf is subtracted. |
| C4 closure iff h_inf >= D_C^Sp | VALID CONDITIONAL | Only a conditional closure criterion; no actual h_inf. |
| CFTH = corrected donor + TC-A..H/TC-S | CONDITIONAL HYPOTHESIS | Sufficient on paper for C1/C3, but no complete C is known to satisfy CFTH; CFTH already includes TC-B/TC-C target properties, so it is not a proof of those properties. |
| C1 finite lower bound | CONDITIONAL | Depends on T15/H_p^Sp, which are inferred consequences, and on CFTH. |
| No global closure claim | CORRECT | The file explicitly withdraws unconditional closure. |

The residual formula is exact given C1; the file is clear that CFTH is
sufficient but unproved. No new attack or new arbitrary assumption is needed.

### 2.2 B=O_K vs B=I

| item | status | comment |
|---|---|---|
| B=O_K/B=I local algebra and trace decomposition | VALID local algebra | I/J=U direct-sum W, l=U, W=ker Tr; independent of Kondo. |
| B_H=O_K for H=Phi^{-1}(Sp) under natural alignment | CONDITIONAL | H fixes U, so the subgroup H does not move l. |
| B_Gamma=O_K for full barGamma | NOT PROVED | Requires every actual source generator to fix l; MODP-BRANCH-PROOF leaves full barGamma undetermined. |
| B_Gamma=I | CONDITIONAL POSSIBILITY only | If an actual gamma moves l, or alignment fails with v!=0; no actual source witness. |
| Corrected global b=3 B=O_K residual 408/41 | CONDITIONAL on full barGamma fixing l | Natural alignment alone gives only B_H=O_K. |
| Corrected global b=273 B=O_K residual 38883/41 | CONDITIONAL on full barGamma fixing l | If B=I, residual 38463/41; both positive, so b=273 conclusion robust. |
| b=3 B=I value 9/41 | NOT ACTUAL under natural alignment | Conditional branch value; b=3 local surplus unavailable unless extra gamma moves l. |

Label issue: GLOBAL-ASSEMBLY-CORRECTED line 137 says "B=O_K branch under the
natural trace alignment". The natural alignment fixes the 2025/2026 basis and
the H-subgroup action, but it does not prove that all of barGamma lies in the
parabolic stabilizer of l. The sentence should say "B_H=O_K for the subgroup H;
full barGamma still needs the first-column test". This is a real conditional
gap, not a numerical error.

### 2.3 Archimedean maximal-container bound and radii

| item | status | comment |
|---|---|---|
| Single-factor shell I_v={|a|<=pi} | VALID paper-level | IUT III Rmk1.2.2(ii). |
| Tensor container pi^{j+1}B_I | VALID paper-level/conditional source | IV Prop1.5(iii)(iv); source container, not attained radius. |
| r_v<=pi as source theorem | INVALID/UNPROVED | Extra hypothesis; corrected global correctly says shell branch not proved. |
| h_inf<=A_arc=((l+5)/4)log pi | VALID CONDITIONAL source-container bound | l=41, A_arc~13.164394; donor-independent but paper-level. |
| Arch-only impossible for b=3/273 | VALID CONDITIONAL | b=3 D>=37.43 (in fact ~93.715 for p=12301) > A_arc; b=273 larger. |
| C6 log(r/pi)>=D for F=Q | VALID CONDITIONAL on radial hull | If non-radial, A6 angular term must be included; C6 is not the full readout. |
| C7 r>=pi p^{d_p} | VALID formula | Base is p, not e. |
| D1/D2 of corrected global | INVALID radii | Use base 41; must be replaced by pi p^{d_p}. |
| Product formula C8/C9 | VALID CONDITIONAL paper-level | Point-modulus constraint, not hull lower bound; does not force positive h_inf. |

The maximal-container comparison is a key correction: it excludes
archimedean-only compensation for the stated conditional profiles, but it does
not prove h_C>=Q_C because other finite places/good contributions are not
bounded and CFTH/TC are open.

### 2.4 Labels

| label | status | comment |
|---|---|---|
| d_p = D_p^Sp/log p | VALID definition | Dimensionless rational, not natural log. |
| Q_p-H_p^Sp (log p) in corrected table | LABEL AMBIGUITY | Values 408/41, 38883/41 are d_p dimensionless; header should say "in log p units" or "d_p", not multiply by log p. |
| A_arc = ((l+5)/4)log pi | VALID paper-level label | Natural log; comparison with finite deficit must use natural logs, not log-p units without conversion. |
| r_inf >= pi*41^{d_p} | INVALID label/base | Correct: pi*p^{d_p}. |
| "B=O_K under natural alignment" | CONDITIONAL/OVERCLAIM | H-subgroup only; full barGamma undetermined. |
| "B=I local surplus 9/41" | CONDITIONAL/NOT ACTUAL | Under inferred alignment B=O_K; only if extra gamma moves l. |

## 3. Exact recomputation

Uniform rho=1, e=41, m0=20, p=12301, B=O_K conditional.

For b=3:

    d_p = 3*42/12 - 2/41 - 1/2 = 10.5 - 0.0487804878 - 0.5
        = 408/41 = 9.9512195122.
    H_p^Sp/log p = -411/41.
    Q_p/log p = -3/41.
    D_p^Sp natural = (408/41) log 12301 ~ 93.7149712746.

For b=273:

    d_p = 273*42/12 - 272/41 - 1/2
        = 955.5 - 6.6341463415 - 0.5 = 38883/41 = 948.3658536585.
    H_p^Sp/log p = -39156/41.
    Q_p/log p = -273/41.
    D_p^Sp natural = (38883/41) log 12301 ~ 8931.1745786033.

B=I conditional values (not actual under natural alignment):

    b=3:   h_B=9/41, Q-h_B=-12/41.
    b=273: h_B=-38736/41, Q-h_B=38463/41.

b=1347 uniform rho=1 (not needed for the main labels, for completeness):

    d_p = 1347*42/12 - 1346/41 - 1/2 = 191928/41 = 4681.1707317073.

b=1347 rho=1/2 direct-domain: the finite lower bound already exceeds Q_p
(direct gap -6784199/429916160), so no archimedean compensation is needed for
that local profile. This is separate from the uniform b=3/273 radii.

Radius values:

    b=3:
      d_p = 408/41.
      log10 p^{d_p} = (408/41)*log10(12301) = 40.6998948963.
      log10 r_inf = 40.6998948963 + log10(pi) = 41.1970447690.
      r_inf ~ 1.5741451259e41.
      Old pi*41^{408/41} ~ 3.51816e16 is invalid.

    b=273:
      d_p = 38883/41.
      log10 p^{d_p} = (38883/41)*log10(12301) = 3878.7598364020.
      log10 r_inf = 3878.7598364020 + 0.4971498727 = 3879.2569862747.
      r_inf ~ 10^{3879.2569862747}.
      Old log10 ~1530.0 is invalid; the correct radius is about 10^{2349}
      times larger.

Max-container comparison:

    A_arc = ((41+5)/4) log pi = 11.5 log pi ~ 13.164394.
    b=3 finite deficit natural ~93.715 > 13.164.
    b=273 finite deficit natural ~8931.175 >> 13.164.
    Hence archimedean-only compensation cannot cancel these conditional finite
    deficits, independent of the actual radius; this does not supply the
    missing finite good-place/global terms.

## 4. Error ledger for this audit

| id | item | verdict | correction |
|---|---|---|---|
| A1 | GLOBAL-ASSEMBLY-CORRECTED D1/D2 base 41 radii | INVALID | Use pi*p^{d_p}, p=12301; correct values above. |
| A2 | GLOBAL-ASSEMBLY-CORRECTED "B=O_K under natural alignment" for full barGamma | CONDITIONAL/OVERCLAIM | Natural alignment gives B_H=O_K; full barGamma requires first-column test (MODP-BRANCH-PROOF (3.4)/(3.5)). |
| A3 | b=3 B=O_K residual 408/41 as the selected branch | CONDITIONAL | Conditional on barGamma(l)=l; otherwise B=I with -12/41 local surplus, or alignment failure v!=0. |
| A4 | b=273 B=O_K residual 38883/41 as selected branch | CONDITIONAL | Conditional on barGamma(l)=l; B=I gives 38463/41, still positive; no closure either way. |
| A5 | b=3 B=I 9/41 as actual/available | INVALID/NOT ACTUAL | Under inferred natural alignment B=O_K; B=I not actual. |
| A6 | shell branch r_v<=pi as source containment | INVALID as source theorem | Extra hypothesis; source container is pi^{j+1}B_I, not I_v. |
| A7 | omitted A_arc max-container bound | INCOMPLETE | Add h_inf<=A_arc~13.164; arch-only impossible for b=3/273 conditional profiles, but no global closure. |
| A8 | table header Q_p-H_p^Sp (log p) | LABEL AMBIGUITY | Values are d_p dimensionless; header should identify log-p units explicitly. |
| A9 | any global h_C>=Q_C / global counterexample | INVALID as proved | CFTH/TC and complete C are open; no global closure or counterexample. |
| A10 | CFTH conditional assembly | VALID CONDITIONAL | It is a sufficient hypothesis package, not a proof of its TC-B/TC-C target properties; no complete C is known. |

## 5. Dependency ledger under the corrected donor

VALID (paper/local exact):

- residual algebra C2/C3 and the closure criterion C4 (conditional);
- local trace/U-W decomposition and B_H=O_K for the subgroup H under natural
  alignment;
- single-factor shell I_v and the tensor container pi^{j+1}B_I as source
  statements;
- radial formula h_inf=log(r/pi) for F=Q, radial hull;
- product formula C8/C9 as a point-modulus constraint;
- exact d_p=408/41, 38883/41 and h_A/h_B values.

CONDITIONAL:

- CFTH and C1/C3 as actual complete-C statements;
- B_Gamma=O_K/B_Gamma=I (full barGamma branch undetermined);
- b=3/b=273 B=O_K residuals (additional barGamma(l)=l);
- b=3 B=I 9/41 (only if extra gamma moves l / alignment fails);
- arch maximal-container bound A_arc (paper-level but not independently re-read);
- C4/C6/C7 compensation criteria (no actual radius);
- product formula as a hull-volume statement (only point modulus).

INVALID / WITHDRAWN:

- D1/D2 radii with base 41;
- B=O_K as a full-barGamma theorem from natural alignment alone;
- shell containment r_v<=pi as a source theorem;
- any unconditional h_C>=Q_C or global counterexample;
- any use of TAME (11)-(14) as target containment or volume proof.

## 6. Remaining gaps

1. Full barGamma branch: compute actual source generators on I/J in the
   trace-adapted basis, or prove all have W-component zero; decide B=O_K/B=I
   without assuming natural alignment for the full image.
2. Basis alignment T / v: compute T e_1 or prove P_W(T e_1)=0.
3. CFTH/TC: supply TC-A..TC-H and TC-S for an actual complete C.
4. Actual archimedean hull/radius and angular term; compare to A_arc; the
   maximal container bound already excludes arch-only compensation for the
   stated conditional profiles, but does not supply global finite/good terms.
5. Complete global weights/places and fixed q/Theta/target-column class.
6. Only then decide global h_C>=Q_C or a genuine counterexample.

## 7. Acceptance record

- Natural-language audit only; no Lean/Project/target edits.
- Residual formula, B-branch labels, and arch radii audited and recomputed.
- b=3/b=273 arithmetic reproduced exactly; corrected base p=12301 radii given.
- No global closure claimed by corrected global assembly; this audit confirms
  that status and records the remaining gaps.
- statement_compiles=false, proof_body_checked=false, kernel_closed=false,
  target_accepted=false.
- No new attack, no arbitrary assumption, no fabricated closure.
