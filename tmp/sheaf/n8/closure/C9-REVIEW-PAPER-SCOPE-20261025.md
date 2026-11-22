# C9 review: paper-level Cor3.12 unconditionality and scope

Task: task-427. Reviewer: qside. Date: 2026-10-25.
Review only: accept/reject exact; no rewrite, no new proof, no Lean, no
Project/target edits, no mixed/E3; only this file written.

## 0. Reviewed material

Source:
- IUT-III.txt SHA256
  822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.
- Theorem 3.11 lines 8999-9460; Corollary 3.12 lines 10152-10180;
  proof Steps (x)-(xi) lines 10520-10780; Step (xi-f) lines 10705-10715.

C9 reviews/claims:
- C9-REVIEW-COR312-QSIDE-20261025.md (task-413).
- C9-REVIEW-COR312-XIF-20261025.md (task-421).
- C9-P6-CAN-NATURAL-PROOF-20261025.md (claims complete P6_can).
- C9-CAN-MASTER-20261025.md (conditional/vs gaps).
- C9-P6-TARGET-DECISION-20261025.md (P6_can primary target).
- C9-SMOOTH-ARCH-ARBITRATION-20261025.md (h_C=h_bad/d+h_inf).

## 1. Summary verdict

ACCEPT:
- Corollary 3.12 as a paper-level theorem under the stated hypotheses of
  Theorem 3.11 and the fixed initial Theta-data.
- Its universal quantification over admissible source data: no explicit
  complete C is constructed or needed.
- Its exact conclusion in the source packet+procession normalization:
  -|log Theta| in R, -|log Theta| >= -|log q|, C_Theta >= -1.
- The conditional implication Cor3.12 + exact T_can => P6_can.

REJECT:
- Calling Cor3.12 "unconditional" in the sense of hypothesis-free or
  applicable outside its source scope.
- Calling the paper-level theorem a proof of P6 without the C9 target
  translation T_can and without normalization/arch comparison.
- Using Cor3.12 to prove P6_norm, global h_C=h_can/d, mixed Q_can<=h_C, or
  any arch lower bound.
- Claiming that the paper's xi-f approximate wording is fully expanded at
  journal-proof level for an independent formalization; the paper asserts it,
  but the natural-language expansion is not complete.
- Claiming an explicit complete C is required for P6 true; it is not.

The paper theorem is accepted **within its scope**: a universal source-level
inequality for Theta-pilot/q-pilot packet log-volumes, conditional on the
Theorem 3.11 setup. It is not a hypothesis-free P6 theorem.

## 2. Exact paper-level statement and hypotheses

Corollary 3.12 begins (lines 10152-10153): "Suppose that we are in the
situation of Theorem 3.11."  Theorem 3.11 (lines 8999-9007) fixes:

- a collection of initial Theta-data
      (F/F, X_F, l, C_K, V, V_bad, epsilon)
  as in IUT I Definition 3.1;
- a collection of distinct Theta±ellNF-Hodge theaters
      { n,m HT^{Theta±ellNF} }_{n,m in Z}
  relative to the given initial Theta-data, regarded as arising from an
  LGP-Gaussian log-theta-lattice (Definition 3.8(iii));
- the associated procession of D^dashv-prime-strips and the data
  (a),(b),(c) with Ind1/Ind2/Ind3.

Under these hypotheses Cor3.12 defines the log-volumes and proves

    -|log(Theta)| in R,
    -|log(Theta)| >= -|log(q)|,
    C_Theta >= -1.

Thus the exact paper-level hypotheses are:
(H1) admissible initial Theta-data in the source sense;
(H2) the Theorem 3.11 LGP-Gaussian log-theta-lattice/procession and
     multiradial representation;
(H3) the Kummer isomorphisms/log-Kummer correspondence;
(H4) the Ind1/Ind2/Ind3 treatment;
(H5) the packet+procession normalization of Proposition 3.9.

ACCEPT Cor3.12 under H1-H5.  REJECT any statement that omits H1-H5 or treats
them as automatic for an arbitrary C9 target.

## 3. What "unconditional" can and cannot mean

ACCEPT "unconditional" in the following limited paper-level sense:
- no extra unproved conjecture beyond the source hypotheses H1-H5;
- no explicit complete C construction is needed;
- the statement is universal over the fixed admissible initial Theta-data.

REJECT "unconditional" in the following senses:
- no hypotheses at all;
- applicable to an arbitrary C9 target hull/native q without T_can;
- applicable to C6 normalized finite-block h_C/Q_C without the factor
  d=41 and arch comparison;
- a proof of P6_norm without h_inf>=0;
- a proof of B=I, kappa, arch positivity, or an explicit C.

The paper does not claim any of the rejected items in Cor3.12.  The theorem is
a source-level inequality, not a C9 P6 theorem by itself.

## 4. Per-claim accept/reject

### P1. Cor3.12 is a paper theorem in its stated scope

ACCEPT.  The source statement and proof place it under Theorem 3.11; the
conclusion is exactly the displayed inequality.

### P2. Cor3.12 is "unconditional" with no hypotheses

REJECT.  It explicitly supposes the Theorem 3.11 situation; H1-H5 are
hypotheses.  "No explicit C" is not "no hypotheses".

### P3. Cor3.12 is universal over admissible C

ACCEPT with the source meaning of "admissible": fixed initial Theta-data
satisfying H1-H5.  REJECT if "admissible" is silently enlarged to include
unconstructed C9 data or a different normalization.

### P4. The xi-f approximation is a numerical epsilon-free exact step

REJECT as an independent expansion.  The source says "perhaps only up to some
sort of 'approximation', as a result of various indeterminacies" (lines
10705-10711) and then asserts the inclusion follows formally (lines
10711-10715).  At paper level this is a source assertion under the
indeterminacy quotient; it is not an expanded set-theoretic membership proof
and it supplies no explicit epsilon/sign.  ACCEPT the assertion only as the
paper's formal step, not as a complete natural-language derivation.

### P5. Cor3.12 alone proves P6

REJECT.  Cor3.12 gives Q_III <= H_III in the source packet+procession
normalization.  P6 requires the C9 identification

    Q_C = Q_III,   h_C = H_III

(or the exact arch-corrected version if using normalized h_C).  That is
T_can/N1-N4, not part of Cor3.12.

### P6. Cor3.12 proves P6_can

ACCEPT only conditionally:
    Cor3.12 + exact T_can  =>  P6_can.
REJECT as an unconditional paper-only consequence.

### P7. Cor3.12 proves P6_norm or handles C6 normalized h_C

REJECT.  Cor3.12 is in packet+procession normalization.  The C6 finite block
has factor 1/d and the C6/C9 global h_C is
    h_C = h_bad_can/d + h_inf,
while the source h_can = h_bad_can + h_inf.  Hence
    h_can = d*h_C - (d-1)*h_inf,
and P6_norm requires h_inf>=0 or the exact arch-corrected target.  Cor3.12
does not supply h_inf>=0.

### P8. Cor3.12 proves global h_C=h_can/d

REJECT.  The arch component is not divided by d; the formula fails unless
h_inf=0 or d=1.

### P9. Cor3.12 proves mixed Q_can<=h_C

REJECT.  This is off by d and arch; the source gives
Q_can<=d*h_C-(d-1)h_inf, not Q_can<=h_C.

### P10. Cor3.12 proves or excludes B=I/B=O_K, kappa, arch positivity,
        or an explicit C

REJECT.  These are outside its scope.  Cor3.12 is a log-volume inequality
for Theta-pilot/q-pilot; it does not determine the B branch, kappa, h_inf,
or construct a C.

### P11. P6 true requires an explicit complete C

REJECT.  P6 true is universal; the Cor3.12 schema is universal over H1-H5
and does not require constructing an explicit C.  P6 false would require an
explicit C, but that is a different direction.

### P12. The paper proof is fully expanded for a no-black-box formalization

REJECT at the level of C9's natural-language audit.  The source leaves the
determinant/log-volume details "to the reader" (Remark3.9.5 Ob3) and qualifies
xi-f with "perhaps only up to approximation".  This does not invalidate the
paper theorem; it does mean any independent C9 expansion must treat A2/A3 as
source obligations, not as already expanded proofs.

## 5. Exact scope boundaries

IN SCOPE of Cor3.12:
- Theta-pilot object from theta values (Definition3.8(i));
- possible images and multiradial representation;
- holomorphic hull of the union of possible images;
- procession-normalized mono-analytic log-volume;
- q-pilot object and its log-volume;
- the inequality Q_III<=H_III and C_Theta>=-1;
- universal over fixed initial Theta-data satisfying Theorem3.11.

OUT OF SCOPE of Cor3.12:
- the C9 abstract target hull/native q identification T_can;
- C6 finite-block normalizedLogVolume and factor d;
- global mixed finite+arch h_C without the exact arch formula;
- P6_norm without h_inf>=0;
- any B=O_K/B=I, kappa, H_A-full, B_I-arch, h_inf lower bound;
- any explicit complete C or E_546-specific construction;
- any assertion that the xi-f approximation has been expanded into an exact
  set-theoretic map.

## 6. Accept/reject table

| # | claim | verdict |
|---|---|---|
| P1 | Cor3.12 paper theorem in stated scope | ACCEPT |
| P2 | Cor3.12 hypothesis-free | REJECT |
| P3 | universal over admissible source data | ACCEPT with H1-H5; REJECT if enlarged |
| P4 | xi-f approximation eliminated/exact expansion | REJECT as expansion; ACCEPT as paper assertion |
| P5 | Cor3.12 alone proves P6 | REJECT |
| P6 | Cor3.12 + exact T_can => P6_can | ACCEPT conditional |
| P7 | Cor3.12 proves P6_norm/C6 normalized | REJECT without d/arch/h_inf |
| P8 | global h_C=h_can/d | REJECT |
| P9 | mixed Q_can<=h_C | REJECT |
| P10 | B branch/kappa/arch positivity/explicit C | REJECT (out of scope) |
| P11 | P6 true needs explicit C | REJECT |
| P12 | paper proof fully expanded for no-black-box audit | REJECT (source assertions remain to expand) |

## 7. Conclusion

Paper-level verdict: Corollary 3.12 is ACCEPTED as a universal source-level
theorem under the Theorem 3.11 hypotheses and packet+procession normalization.
It is NOT accepted as a hypothesis-free or C9-normalization-free P6 theorem.
The xi-f approximation qualifier is accepted only as the paper's formal
indeterminacy step; it is not an expanded exact membership proof.  P6_can is
accepted as a conditional consequence of Cor3.12 plus exact T_can.  P6_norm,
global h_C=h_can/d, mixed Q_can<=h_C, and any B/arch/kappa conclusion are
rejected as out of scope.

No Lean, no Project/target edits, no mixed/E3. target_accepted=false; P6
remains open.

## 8. Sources

- IUT III Theorem 3.11, Cor 3.12, Step (xi): sources/IUT-III.txt SHA256
  822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.
- C9-REVIEW-COR312-QSIDE-20261025.md; C9-REVIEW-COR312-XIF-20261025.md.
- C9-CAN-MASTER-20261025.md; C9-P6-TARGET-DECISION-20261025.md.
- C9-SMOOTH-ARCH-ARBITRATION-20261025.md.
