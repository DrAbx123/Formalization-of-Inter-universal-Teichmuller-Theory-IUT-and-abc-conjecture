# C9 review: scope/no-substitution in the NL P6_can proof

Task: task-414 (Review scope/no-substitution in NL proof). Owner: volumedet.
Date: 2026-10-25. Review only; no rewrite. No Lean/Project edits, no mixed/E3.
Only this file written. `target_accepted=false`.

Reviewed file: `C9-P6-CAN-NATURAL-PROOF-20261025.md` (162 lines).

## 0. Verdict

**Scope/no-substitution: ACCEPT.** The proof consistently states the paper
packet+procession-normalized P6_can and explicitly disclaims the C6
finite-block normalized target. It uses no mixed/E3 profile, no row max, no
normalized surrogate, no factor 41, no separate arch h_inf substitution, no
numerical epsilon, and no b=273 no-go.

**As a complete unconditional proof: REJECT.** The proof is a source schema
conditional on A1-A3 and T_can; A2/A3 are not expanded to exact source
statements, several labels (`sQ1`-`sQ4`, `cQ3`, `cQ4`, `citw`) are used without
exact source definitions, and T_can is a target identification by definition,
not a theorem. It therefore cannot be accepted as a completed proof of
P6_can without those exact source steps.

The distinction is important: the failure is **completeness**, not a
prohibited scope substitution.

## 1. Prohibited-substitution checklist

| prohibited item | present? | review |
|---|---|---|
| mixed profile (rho in (0,1)) | NO | proof keeps uniform all-bad profiles; no mixed avg |
| row max/sup instead of procession average | NO | explicitly procession average over j in F_l^* |
| normalized surrogate (C6 1/D) | NO | proof uses packet+procession; T_can explicitly rejects C6 normalized target |
| factor 41 | NO | no d=41 in Q_can/h_can; q-pilot 82-root built into Q_can; no 82 either |
| separate arch h_inf substitution | NO | h_can is the full source log-volume including arch; no C9 h_inf used |
| numerical epsilon | NO | A3 uses formal quotient/indeterminacies; no epsilon estimate |
| b=273 no-go | NO | no b=273 special case or exclusion |
| arbitrary B branch/U-B normalization | NO | no B=O_K/B=I branch used |

So the proof stays inside the paper P6_can scope as stated.

## 2. Scope details

- Convention §0 matches the source packet normalization (log(O)=0,
  multiplication by p adds -log p, by e adds 1) and procession average over
  j in F_l^*. This is not the C6 finite-block 1/D convention.
- The target is `Q_can<=h_can` with Q_can=-|log q|, h_can=-|log Θ|. T_can
  explicitly distinguishes this from the C6 normalized finite target and
  says that target would require an arch comparator. That is correct scope
  discipline.
- The q-pilot 82-root normalization is included in Q_can; no extra 82.
- There is no attempt to use the normalized Lean target as a surrogate.
- There is no arch h_inf term or B_I-zero factor in the core proof; the
  source h_can includes arch by definition. This is not a substitution.

## 3. Completeness gaps (reasons for REJECT as complete proof)

### G1. A1 source link not fully extracted

A1 asserts the q-pilot F^value×mu input is fixed/coric and that the
multiradial algorithm outputs data linked by a full poly-isomorphism with
F^value full and F^unit×mu subject to Ind1/2/3. The cited loci
(Def3.8(i), Rem3.11.1(ii), Thm3.11) are plausible, but the proof does not
quote the exact source statement of the F^value/F^unit split or verify its
compatibility with Ind1/2/3. This is a source-expansion gap, not a scope
violation.

### G2. A2 determinant/bundle comparison is asserted, not constructed

A2 says the hull H(C) determines an arithmetic vector bundle E_H of rank>1
and defines `L_H=det^M(E_H)⊗det^M(O(-))^{-1}` with
`deg(L_H)/M=h_can`, `deg(L_q)=Q_can`. The proof cites Remark3.9.5
Ob1-Ob3 but does not construct E_H, prove the determinant normalization/
`O(-)` adjustment has degree zero, or verify the exact degree identity in
the common packet normalization. This is the main missing computation.

### G3. A3 is a chain of source labels, not an exact proof

A3 uses `sQ1`, `sQ2`, `sQ3`, `sQ4`, `cQ3`, `cQ4`, `citw`, `Ob9`, `AND`,
`q-itw`, `Theta-itw` without defining all of them by exact source loci. The
key conclusion `Q_can in R_{<=h_can}` is essentially the desired semantic
inclusion; the proof's `closed loop`/`AND` argument does not expand it into
the source's Step (xi-e)/(xi-f) statements. No numerical epsilon is used,
but no exact source verification/construction is supplied either.

### G4. T_can is definitional

T_can identifies the C9 hull/q-pilot with the III source objects. That is a
target-identification statement (correct for paper P6_can), not a theorem
that fills G1-G3. It cannot be used to prove A3.

### G5. Universal quantifier

The theorem claims 'for every admissible C'. Cor3.12 is universal over the
source initial data, so this quantifier is legitimate only if A1-A3 are
source theorems for every admissible C. The proof supplies citations, not
the exact universal source verification.

## 4. No prohibited substitution found

Specifically:

- No mixed profile or row max: the procession average and all-bad profile
  are used.
- No normalized surrogate: the proof's T_can explicitly rejects the C6
  1/D target; the core Q_can/h_can are source packet objects.
- No factor 41: the proof does not insert d=41; q-pilot 82-root is inside
  Q_can.
- No arch h_inf substitution: the source h_can includes its own arch term;
  the proof does not replace it by C6 h_inf.
- No numerical epsilon: A3 is formal/semantic, with no epsilon estimate.
- No b=273 no-go: no b-specific exclusion.

Thus the **scope** is paper P6_can; the **proof** is not complete.

## 5. Accept/Reject

**ACCEPT**: scope and no-substitution discipline.

**REJECT**: acceptance as a complete natural-language proof of P6_can. Reason:
A1-A3/T_can are a conditional source schema. A2 and A3 are the critical
missing source expansions; without them the theorem is conditional, not
proved. This is not a request to rewrite the proof and not a rejection for
prohibited substitutions.

Status if one insists on binary: `scope=ACCEPT`, `proof=REJECT/conditional`.

## 6. Classification

PROVED/ACCEPTED (review scope):

- Paper packet+procession P6_can scope.
- No mixed/E3, row max, normalized surrogate, factor 41, arch h_inf
  substitution, numerical epsilon, b=273 no-go.

NOT ACCEPTED (completeness):

- A1 exact source split; A2 bundle/determinant computation; A3 source
  closed-loop/xi-e/f expansion; T_can definitional only.

## 7. Status

Review only. No rewrite. No Lean/Project edits, no mixed/E3. Only this file
written. `target_accepted=false`; scope accepted; complete proof not accepted.
