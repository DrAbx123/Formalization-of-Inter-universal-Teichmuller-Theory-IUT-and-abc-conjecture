# C9 independent audit: master contradiction route

Task: task-187. Date: 2026-10-25. Auditor: transport.
Stage: read-only natural-language audit. No Lean/Project edits.
Only this file written. target_accepted=false.

## 0. Audited bytes

Primary file:

| file | lines | SHA256 |
|---|---:|---|
| C9-MASTER-CONTRADICTION-20261025.md (current task-178 final) | 498 | 362CBD36C95B2BBCB1A0395E7E99DF3131DCB82E8E1BC5441330CFF8571D48A1 |

The current 498-line/362CBD... bytes were used, not the older 464-line
968834... version.

Spot-check inputs:

| file | lines | SHA256 |
|---|---:|---|
| C9-CANONICAL-NORM-ATTACK-20261025.md | 314 | B13902F60B129135B33324E763880DA5C90B175A83E0E639293D3844DD48408B |
| C9-NORMALIZATION-DECISION-20261025.md | 267 | 5E969DFBFB3E08B2C2CA5A7859683F914FEB3236486B51691FD4D77BE774C78D |
| C9-AUDIT-B-TYPEGAP-20261025.md | 127 | 540825E769E9F2895CE2FA327719C9A5A1F46BFA751E8865CB2A16E4322BAB27 |

## 1. Verdict

MASTER_ROUTE_AUDIT = VERDICT SUPPORTED, WITH QUALIFICATIONS.

The executive verdict "no contradiction is reached; P6 is open; no complete
counterexample is produced" is correct for the current corpus. The four
failure layers are correctly identified. The C1-C43 ledger is substantially
correct, but three labels/wording need correction:

1. C13 (trace table/U/W) must be CONDITIONAL on the inferred trace-basis
   alignment, not PROVED.
2. C37 (D/Aut(K) cannot produce B=I) is a limited subgroup statement, not a
   full-Out theorem; label should be CONDITIONAL, not PROVED.
3. The phrase "B branch is type-gapped" and the headline "no actual finite
   compensation exists" are valid as statements about the current corpus's
   missing data/constructions, but not as proved mathematical non-existence.
   They must be read as "not defined/constructed by the cited data".

No overclaim changes the main verdict. The E15 factor d, E19 B_I-zero
normalization, b=3/b=273 arithmetic, and O1-O7 obstruction list are confirmed.

## 2. Executive verdict and four failure layers

### 2.1 No contradiction

The master does not produce an actual complete C with Delta>0, nor derive a
contradiction. Its own Sections 5.1-5.4 show:

- only a conditional finite lower bound and an archimedean upper bound;
- B branch is not source-defined in the current corpus;
- target container/volume preservation is missing;
- canonical/normalized Q and arch normalization conventions require conversion.

Therefore "no contradiction reached" is CORRECT.

### 2.2 Four failure layers

The four failure layers are:

1. Finite lower bound never reaches Q_C with the available arch upper bound.
2. B=I is not actual; B branch is not source-defined; B=O_K for full barGamma
   is not proved.
3. Target container/normalized volume is missing (TC-A..H/TC-S).
4. Canonical/normalized Q factor d and arch normalization gaps.

These are independent and each independently blocks the route. The subsections
5.1-5.4 correctly state them. Section 5.5 is not a fifth failure layer; it is
the list of what a successful contradiction would require. The phrase "four
independent layers" is therefore consistent with 5.1-5.4.

### 2.3 Layer 5.1 arithmetic

For b=3, B=O_K conditional:

    h_C >= -(411/41)log12301 + h_inf,
    Q_C = -(3/41)log12301,
    h_inf >= (408/41)log12301 = 93.714971...

Only the arch upper bound A_arc=11.5logpi=13.164 is available. An upper bound
cannot supply this lower bound. The statement that the conditional lower bound
is below Q_C and permits a deficit is CORRECT.

### 2.4 Layer 5.2 branch qualification

B=I is indeed not actual in the frozen sources; B=O_K for full barGamma is also
not proved. The route cannot use either branch as an actual contradiction.

Wording qualification: "type-gapped" should mean the branch is not defined by
the cited data (no H_A-full integral lift, no full-Out matrices on I/J), not
that a mathematical impossibility has been proved. The master's E16/E20 say
the cited papers do not prove preservation/lift; they do not prove no lift can
exist. The audit accepts "not source-defined/current-corpus gap"; it does not
accept "mathematically impossible".

## 3. E15 factor d and E19 normalization

### 3.1 E15 canonical/normalized factor

The canonical-norm attack audited by C9-CANONICAL-NORM-ATTACK establishes:

    log ||x||_canon = d * log ||x||_norm,
    d = [F_v:Q_p] = relativeCompletionDegree = e f.

For the paper q candidate:

    localSignedLog(qCandidate) = d * PaperQLog,
    QPaper.qPilotLogVolume = d * PaperQLog   (if C3.q=qCandidate).

In the tame totally ramified C9 type d=e=41, not 1.

Consequences:

- C9Paper Q is canonical; Theta is C6-normalized.
- Q<=Theta and QPaperInRleq mix conventions unless Q is divided by d or Theta
  multiplied by d.
- Master C34/C35/C36 are CORRECT: canonical=normalized is invalid for d>1;
  Q<=Theta is invalid without conversion; the conversion is exact.

This is a genuine independent gap and the master correctly records it.

### 3.2 E19 binding normalization

The master applies the binding B_I-zero convention:

    F=Q radial: h_inf=log r_inf,
    shell r<=pi: h_inf<=log pi=1.1447298858, not 0,
    max container A_arc=11.5logpi=13.164394,
    compensation radius r_inf>=p^{d_p}, no pi factor.

This matches task-182. The old shell-pi forms h_inf=log(r/pi), h_inf<=0, and
r>=pi*p^{d_p} are correctly WITHDRAWN as binding. The master does not use
A_arc as a lower bound; it explicitly says an upper bound cannot prove
h_C>=Q_C. CORRECT.

## 4. Claim ledger C1-C43

The master's ledger actually contains C1-C46. The task's C1-C43 range is
covered; C44-C46 are additional corrections from E20 and E19. No claim is
missing from C1-C43.

### 4.1 Confirmed PROVED/paper-level claims

- C3 Phi closed and Sp containment: PROVED paper-level (Kondo 2026).
- C5 rho not homomorphism; D fixes x1/y1 in k_+: PROVED paper/local.
- C6 Aut(K) fixes l=O_K/J: PROVED field theory.
- C7 y_i in J and zero in I/J; y-basis not an I/J basis: PROVED local.
- C15 d_p/h_A/h_B arithmetic: PROVED arithmetic (branch-conditional as values).
- C23 h_inf<=A_arc: VALID conditional upper bound.
- C25 shell h_inf<=log pi, C26 radius p^{d_p}: VALID under binding B_I-zero.
- C31 aggregate B=I counts: VALID arithmetic conditional.
- C36 canonical/normalized conversion: VALID arithmetic.
- C43 E1-E20 incorporated: status ledger is accurate.

### 4.2 Corrections to labels

C13 (trace table/U/W) is labelled PROVED local algebra. This is correct for
the pi-power/trace computation, but the identification of the Kondo trace basis
with the 2026 symplectic basis is inferred, not a paper theorem (task-147).
Therefore the decomposition U/W as an actual C9 object is CONDITIONAL on the
basis-alignment convention. Correction: C13 should be CONDITIONAL/INFERRED for
the U/W identification; only the pi-power trace table is PROVED.

C37 (D/Aut(K) cannot produce B=I) is labelled PROVED conditional. What is
proved is:

- the mapping-class D fixes x1/y1 in k_+
- field Aut(K) fixes O_K,J and l=O_K/J.

This does not prove that no element of full Out can move l, nor that B=I has no
source generator. The claim should be limited to D/Aut(K) and labelled
CONDITIONAL/limited, not a full-Out theorem.

C28 (no actual finite compensation) is marked CONDITIONAL/UNKNOWN in the
ledger, which is correct. The executive summary phrase "No actual finite
compensation exists" is stronger than C28. It should read "no documented
actual finite compensation is constructed in the current corpus". This is a
wording overclaim, not a mathematical falsehood under the intended reading.

### 4.3 Other claims

- C8 full Out preserves O_K,J,I / acts on I/J: NOT PROVED. Correct.
- C9/C10/C11 B branches: conditional/unproved. Correct.
- C12 explicit matrix source: INVALID. Correct.
- C14 J=m/T7/T8/T14/T15: conditional/inferred. Correct.
- C16/C17/C18 residuals: conditional arithmetic; b=3 B=I not actual. Correct.
- C19/C20/C21/C22 TAME target proof/ring-iso/volume/CFTH: WITHDRAWN or
  CONDITIONAL. Correct.
- C24 arch-only compensation: CONDITIONAL. Correct.
- C26b shell-pi forms: WITHDRAWN. Correct.
- C27 old radii: INVALID/WITHDRAWN. Correct.
- C29/C30 other-local positive output/actual compensation: INVALID/NOT PROVED.
  Correct.
- C32/C33 aggregate actual C/B=I impossible: NOT CONSTRUCTED/INVALID. Correct.
- C38 full Q1 well-posed: INVALID/type-gapped. Correct with the same
  "type-gapped = current-data gap" qualification.
- C39-C42 global assembly/contradiction/counterexample: CONDITIONAL/NOT
  PROVED/NOT PRODUCED. Correct.
- C44 TAME full-Gamma dichotomy actual: INVALID AS WRITTEN. Correct.
- C45 B branch source-defined: INVALID. Correct with current-corpus reading.
- C46 B_I-zero binding: DECIDED. Correct.

## 5. Obstruction list O1-O7

| id | master obstruction | audit |
|---|---|---|
| O1 | no actual complete C with H_C/Q_C/weights | VALID; complete C absent |
| O2 | B branch type-gapped: no H_A-full lift/matrices; B=I no source; B=O_K full unproved | VALID as current-data gap; "type-gapped" not a proved impossibility |
| O3 | TC-A..TC-H/TC-S target containment/normalized volume missing | VALID |
| O4 | arch readout only upper bound; actual r/angular term missing | VALID under B_I-zero |
| O5 | canonical vs normalized Q/Theta factor d unresolved | VALID; E15 exact d factor |
| O6 | local finite values conditional; arch upper bound cannot supply lower bound; no actual finite compensation | VALID, with "no documented actual compensation" wording |
| O7 | other local types/f/Delta_shell and aggregate B=I not realized | VALID |

No obstruction is missing for the current route. O2 and O6 carry the wording
qualifications above.

## 6. Independent arithmetic spot checks

### 6.1 b=3

    d_3 = 3*42/12 - 2/41 - 1/2 = 10.5 - 0.0487804878 - 0.5
        = 408/41 = 9.9512195122.
    h_A = -411/41, h_B=9/41, Q=-3/41.
    D_A=408/41, D_B=-12/41.
    natural D_A = (408/41)log12301 = 93.7149712746.
    B_I-zero radius = 12301^{408/41} = 5.0106595585e40,
    log10 = 40.6998948963.

All correct in the master.

### 6.2 b=273

    d_273 = 273*42/12 - 272/41 - 1/2
          = 955.5 - 6.6341463415 - 0.5
          = 38883/41 = 948.3658536585.
    h_A=-39156/41, h_B=-38736/41, Q=-273/41.
    D_A=38883/41, D_B=38463/41.
    natural D_A = (38883/41)log12301 = 8931.17457860.
    B_I-zero radius = 12301^{38883/41}, log10 = 3878.759836402.
    B=I radius = 12301^{38463/41}, log10 = 3836.862885.

Master's table and E6/E10 labels are CORRECT: 38883/41 is A=O_K, 38463/41
is B=I. No branch-label error remains in the current bytes.

### 6.3 Arch constant

    A_arc = (41+5)/4 logpi = 11.5 logpi = 13.1643936873.
    shell bound = logpi = 1.1447298858 (not 0).

Correct.

### 6.4 Canonical d

    d = [F_v:Q_p] = e f; tame totally ramified d=e=41.
    localSignedLog = 41 * PaperQLog.

Correct per E15. The master correctly refuses Q<=Theta without conversion.

## 7. Complete-C gap

The master repeatedly states no complete C is constructed. This is correct:
the p=12301 e=41 model is a local Tate/local-field realization; it does not
supply bad set, good finite places, row/Theta weights, fixed q class, target
column, CFTH/TC, or actual archimedean hull. No global h_C, Q_C, or
counterexample is produced.

The "complete-C gap" is therefore not merely a proof gap: it is the first
obstruction O1 and blocks every global claim.

## 8. Corrections to record

1. C13: CONDITIONAL/INFERRED for U/W identification, not PROVED; pi-power
   trace table remains PROVED.
2. C37: limit to D/Aut(K); full-Out B=I nonproduction is NOT PROVED; label
   CONDITIONAL/limited.
3. "Type-gapped": read as "not source-defined/current-corpus gap", not proved
   non-existence; apply to C38/C44/C45/O2.
4. "No actual finite compensation exists": change to "no documented actual
   finite compensation is constructed"; C28 already has the correct
   CONDITIONAL/UNKNOWN label.
5. Four failure layers: 5.1-5.4 only; 5.5 is requirements, not a fifth layer.
6. C1-C43: master ledger extends to C46; no C1-C43 claim missing; C44-C46 are
   valid additions.

None of these corrections changes the master verdict "no contradiction".

## 9. Final audit verdict

MASTER ROUTE VERDICT: SUPPORTED.

- No contradiction: CONFIRMED.
- Four failure layers 5.1-5.4: CONFIRMED.
- C1-C43 ledger: SUBSTANTIALLY CORRECT; C13/C37 labels and two wording
  claims corrected; C44-C46 valid additions.
- O1-O7: CONFIRMED with O2/O6 wording qualifications.
- E15 factor d: CONFIRMED; no Q<=Theta comparison without conversion.
- E19 B_I-zero: CONFIRMED; h_inf=log r, shell h_inf<=log pi, radius p^{d_p}.
- b=3/b=273 arithmetic and branch labels: CONFIRMED.
- Complete-C gap: CONFIRMED.

No overclaim in the master affects the main verdict. The route is a valid
stage1 negative audit/assembly, not a proof of P6, not a contradiction, and
not a complete counterexample.

target_accepted=false.
