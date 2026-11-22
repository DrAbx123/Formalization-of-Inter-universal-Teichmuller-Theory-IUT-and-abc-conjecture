# C9 review: IUT III Corollary 3.12 and the final P6_can inequality

Task: task-413. Reviewer: qside. Date: 2026-10-25.
Review only: accept/reject with exact reasons. No rewrites, no new proof,
no Lean, no Project/target edits, no mixed/E3; only this file written.

## 0. Reviewed material

Source:
- IUT-III.txt SHA256
  822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D,
  Corollary 3.12 lines 10152-10180; proof Step (xi) lines 10520-10780;
  Remark 3.9.5 Ob3 lines 7770-7868.

C9 claims:
- C9-P6-CAN-NATURAL-PROOF-20261025.md
  SHA256 E78BAD81B1ABE4CD365D77391888C7B4DC74A3B3CC4E5FC83E8F21EB7B58A1C9.
- C9-CAN-MASTER-20261025.md
  SHA256 E87D6CE5AA5E1F08ABA5375EB98963B7EC16617630D39D4A0EE41C21AFB192FB.
- C9-CAN-A3-CLOSEOUT-20261025.md
  SHA256 BAAC9B45E0BEC5A837C0E8F743A5708A5600A840392094A272140508E5B45B94.
- C9-CAN-A3-CLOSED-LOOP-20261025.md
  SHA256 4BAA76F206FC9CD526B470B992F33E53611C88518280F37B771BEC363F5C89EC.
- C9-CAN-A23-AUDIT-20261025.md
  SHA256 266764A6F6CF77E7E035F489C8BE8052225D8C9DA9B17B4C76E6479673F8A761.
- C9-P6-TARGET-DECISION-20261025.md
  SHA256 6A0843E5A05551F58B43C5C31BB33BE34672E850FC00DFD89922C271EAAF7C9C.

## 1. Summary verdict

ACCEPT:
- The statement of IUT III Corollary 3.12 as a source theorem, in its own
  packet+procession normalization and under the Theorem 3.11 situation.
- A1 as a source-input statement.
- P6_can (Q_can<=h_can) as the correct paper/canonical target convention.
- The conditional implication: if A1, A2, A3, and T_can are supplied, then
  P6_can follows; this is a valid logical skeleton.
- The arch arbitration h_C=h_bad_can/d+h_inf (d=41) as the actual C6/C9
  global formula; the exact arch-corrected target
  Q_can/d+((d-1)/d)h_inf<=h_C.

REJECT:
- The claim that P6_can is an unconditional/completed natural-language proof.
- A2 as an exact proved determinant/log-volume identity.
- A3 as an exact set-membership proof.
- T_can as a theorem (rather than a definitional identification/gap).
- The global h_C=h_can/d formula and any P6_norm without h_inf>=0.
- The mixed target Q_can<=h_C.

The final inequality is therefore ACCEPTED ONLY CONDITIONALLY, and the
"COMPLETE NATURAL-LANGUAGE PROOF" label is REJECTED.

## 2. Corollary 3.12 itself: ACCEPT

The source statement at lines 10152-10180 is:

- -|log(Theta)| in R union {+infinity} is the procession-normalized
  mono-analytic log-volume of the holomorphic hull of the union of possible
  images of the Theta-pilot object, subject to Ind1/Ind2/Ind3;
- -|log(q)| in R is the q-pilot log-volume, not subject to Ind1/2/3;
- Cor3.12 proves -|log(Theta)| in R and
      -|log(Theta)| >= -|log(q)|,
  i.e. C_Theta >= -1.

Acceptance reasons:
- This is exactly what the source states; the signs and normalization are
  extracted correctly.
- It is conditional on the Theorem 3.11 multiradial/Ind setup, but it is not
  an arbitrary extra hypothesis; it is the source theorem's own hypothesis.
- It does not require an explicit complete C.

ACCEPT the statement. Do not accept any claim that it is a definitional
consequence or that it is already a C9 P6 theorem without translation.

## 3. A1: ACCEPT

A1 says the q-pilot at (1,0) is a fixed/coric source input, with log-volume
Q_can=-|log q|, not subject to Ind1/2/3, and the multiradial algorithm
outputs possible data linked to it by F^value x mu poly-isomorphisms.

Acceptance reasons:
- Definition 3.8(i) determines the q-pilot by q_v up to torsion; the
  associated global realified Frobenius object is independent of the
  generator collection, so the log-volume is well-defined.
- Step (xi-a)-(xi-e) supports the fixed/coric representation on 1,circ U_Q and
  the output-input link.
- The q-pilot is indeed not subject to Ind1/2/3 in Cor3.12.

Caveat (not a rejection): q_v is up to torsion and IUT III does not display
the numerical formula; Q_can=-(b/41)logp is the C9 82-root calibration, an
explicit calibration input rather than a source-displayed number.

## 4. A2: REJECT as exact proof; ACCEPT as source schema only

A2 claims:
  L_H = det^{tensor M}(E_H) tensor det^{tensor M}(O(-))^{-1},
  deg(L_H)/M = deg(det E_H) = mu_log(H) = h_can,
  deg(L_q) = Q_can.

Rejection reasons:
(A2-1) E_H (rank>1 arithmetic vector bundle) is referenced but not explicitly
       constructed from the hull. Remark3.9.5 Ob1-Ob2 describe it.
(A2-2) The positive tensor power M is not given by an explicit formula.
(A2-3) The O(-) determinant twist/inverse normalization is referenced in
       Ob3; the source says "we leave the routine details to the reader"
       (lines 7819), not an expanded equality.
(A2-4) The exact arithmetic degree/log-volume identity
       deg(det E_H)=mu_log(H) is source-asserted only "up to suitable
       normalization factors" (Ob3-3); the constants are not displayed.
(A2-5) The weights N_v, hull approximant phi(P), tensor-twist invariance,
       upper semi-compatibility, and vertical log-Kummer rectification are
       cited, not proved line by line.
(A2-6) The source comparison is at the level of normalized log-volume
       functionals, not an explicit determinant norm equality.

Therefore A2 is a valid source schema/conditional obligation, not a proved
identity. The phrase "we leave the routine details to the reader" is exactly
the gap; it is not a completed proof.

ACCEPT A2 only as a named source obligation with A2-1..A2-6 open.

## 5. A3: REJECT as exact membership

A3 claims:
  Q_can = -|log q| in R_{<=h_can}, h_can=-|log Theta|.

Rejection reasons:
(A3-1) The source itself says the construction of possible output log-volumes
       constitutes "perhaps only up to some sort of 'approximation', as a
       result of various indeterminacies" (Step xi-f, lines 10705-10711).
       This is not an exact set-membership statement.
(A3-2) The proof's exact inclusion (lines 10712-10715) is source-asserted to
       "follow formally"; it is not derived from an exact map.
(A3-3) The recent closed-loop/fitw reconstruction
       (C9-CAN-A3-CLOSED-LOOP, C9-CAN-A3-CLOSEOUT) is a plausible semantic
       reading: the "approximation" is reinterpreted as the indeterminacy
       quotient. But the subquotient AND of Remark3.9.5(viii), the
       compatibility (cQ3)/(cQ4) of sQ3/sQ4 with the log-Kummer
       correspondence, and the identification of the AND with the AND of
       (citw) are cited, not expanded. CL1-CL3 remain.
(A3-4) There is no explicit signed error epsilon with
       Q_can+epsilon in R_{<=h_can} and epsilon<=0/bounded. Without that,
       "up to approximation" cannot be converted into the exact inequality.

Therefore A3 is not proved. The exact-membership claim is rejected; the
closed-loop interpretation is accepted only as a conditional source reading.
A3 must be either expanded exactly or replaced by an explicit epsilon
statement with sign/bound.

## 6. T_can: REJECT as theorem; ACCEPT only as definitional conditional

T_can claims C9Hull=IIIHull and C9QPilot=IIIQPilot.

- IUT III defines its Theta-pilot hull and q-pilot, but it does not identify
  an abstract C9 target hull/native q with those objects.
- If C9 defines C9Hull/C9QPilot as those source objects and uses the same
  canonical volume functional, T_can is definitional (not a theorem).
- If C9Hull/C9QPilot are abstract objects, T_can is an exact object-identity
  gap; N1-N4/C1a-c/C2a-b must be proved or explicitly assumed.

Thus accept T_can only as "definitional under the paper-target convention";
reject it as an independently proved source theorem.

## 7. Final inequality: ACCEPT conditional, REJECT unconditional/complete

The final P6_can claim is:

  for every admissible C, Q_can(C) <= h_can(C).

Decision:
- ACCEPT the logical implication
      A1 + A2(exact) + A3(exact) + T_can  =>  P6_can.
  The algebra is immediate from Cor3.12 and the identifications; no
  normalized surrogate and no factor d are hidden.
- REJECT the claim that this is a complete proof or that P6_can is proved.
  A2 is a schema, A3 is approximate/source-asserted, and T_can is
  definitional/gapped. The latest C9-CAN-MASTER correctly lists
  SORRY_A2, SORRY_A3, SORRY_TCAN; the C9-P6-CAN-NATURAL-PROOF title
  "COMPLETE NATURAL-LANGUAGE PROOF" overstates the status.

The final inequality is therefore a **conditional theorem skeleton**, not an
established theorem. target_accepted=false is correct.

## 8. Target convention and arch formula: ACCEPT/REJECT

ACCEPT:
- P6_can (Q_can<=h_can) as the paper target.
- h_C = h_bad_can/d + h_inf, d=41, as the actual C6/C9 global formula.
- h_can = d*h_C-(d-1)*h_inf.
- exact target Q_can/d+((d-1)/d)h_inf<=h_C.
- q-pilot Q_can=-b/41 (2l=82 normalization; no extra 82).

REJECT:
- global h_C=h_can/d;
- P6_norm Q_can/d<=h_C without h_inf>=0;
- mixed Q_can<=h_C;
- using the finite normalized Lean target as paper P6_can without the arch
  comparator.

Reasons: the Lean C6 normalizedLogVolume is finite-block only
(FinitePlaceNormalizedUnitScalingLogVolume.lean:89-98, C6ActualIQData.lean:
30-43); the arch h_inf is a separate B_I-zero readout not divided by d. The
uniform-global h_C=h_can/d formula divides the arch term and is not the actual
C6/C9 assembly.

## 9. Exact reasons for rejection in one line each

R1. Cor3.12 source statement: ACCEPT; it is exactly the source theorem.
R2. A1: ACCEPT; source-input/fixed q-pilot, with torsion caveat.
R3. A2: REJECT as proved; determinant/E_H/M/O(-)/degree/log-volume details
    are source-referenced, not displayed; "routine details" left to reader.
R4. A3: REJECT exact membership; source says "perhaps only up to
    approximation"; no signed epsilon; subquotient/AND and cQ3/cQ4 not
    expanded.
R5. T_can: REJECT as theorem; definitional only under paper-target
    identification, otherwise object-identity gap.
R6. Final P6_can: ACCEPT conditional implication; REJECT unconditional or
    "complete proof" claim.
R7. Arch: ACCEPT h_C=h_bad/d+h_inf; REJECT h_C=h_can/d and mixed targets.
R8. P6_norm: REJECT without h_inf>=0 or arch-corrected target.

## 10. Review status

The review is based on the source text and the listed C9 documents. No Lean
build, comparator, kernel check, or target acceptance was run. No mixed/E3
profile is used. No files other than this review were written.

Verdict: Cor3.12 accepted as source theorem; final P6_can accepted only as a
conditional schema; the unconditional/completed-proof claim is rejected.
P6 remains open. target_accepted=false.
