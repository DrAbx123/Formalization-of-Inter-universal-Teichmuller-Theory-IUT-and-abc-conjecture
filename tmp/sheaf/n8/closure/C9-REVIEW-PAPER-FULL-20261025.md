# C9 review: paper-level Cor3.12 proof

Task: task-425. Reviewer: kummer. Date: 2026-10-25.
Review only; no rewrite; no Lean/Project edits; no mixed/E3.
Only this file written. target_accepted=false; P6 open.

## 0. Reviewed file

- C9-COR312-PAPER-PROOF-20261025.md, 100 lines,
  SHA256 91f6bd347d7baba6854bce81ed185a553f536d27615ea4356d2f50f0b818431b.
- Source: IUT-III.txt, SHA256
  822e03da7e2a7402a3bb406d698bb3374401e3fb102058c80864d6c06139353d.

The file explicitly scopes itself as a **paper-level** proof following IUT III
section 3, not a first-principles derivation. The review applies that standard.

## 1. Verdict

**ACCEPT as a paper-level proof; REJECT only if it is presented as a
first-principles or unconditional independent proof.**

The file accurately follows the source's own theorem/xi-e/xi-f structure and
does not overread Theorem3.11/Prop3.9/Remark3.9.5 beyond citing them at the
source level. The remaining caveats are real but consistent with paper-level
scope:

- the source WLOG assumption -|log Theta|<0 is not mentioned;
- the source's "perhaps only up to some sort of approximation" is interpreted
  as the Ind1/2/3 indeterminacy quotient, not independently proved exact;
- the determinant/Ob3 comparison is skipped because xi-f is used as the
  source's own proof step; acceptable at paper level, not first-principles;
- P6_can follows only for paper objects, not for an independently defined C9
  target.

## 2. Section 0: theorem statement — ACCEPT

The theorem statement matches IUT III Corollary 3.12 (lines 10152-10180):
-|log Theta| in R, -|log Theta| >= -|log q|, and C_Theta >= -1.

Accept as source.

## 3. Section 1: setup — ACCEPT

Def3.8(i) q-pilot from q_v up to torsion; Theta-pilot from theta values;
Def3.8(ii) Theta x mu LGP-link full poly-isomorphism; Prop3.9 normalization
(log O=0, p_v adds -log p_v, e adds1, average over F_l^*).

These are accurate source uses.

## 4. Section 2: multiradial representation and finiteness — ACCEPT with caveat

The use of Theorem3.11/Remark3.11.1 for the output possibilities, Ind1/2/3,
IPL/SHE/APT/HIS is paper-level correct.

Finiteness: source lines 10234-10237 derive finiteness of -|log Theta| from
compactness of 1,circ U_{j,vQ} and Prop3.9. The file cites this correctly.

Caveat: the source proof begins with the WLOG assumption
-|log Theta|<0 whenever finite (lines 10181-10185); if -|log Theta|>=0 the
inequality is immediate. The file does not mention this branch. This is a
minor omission at paper level, because the source theorem statement covers it
and the inequality is trivial in that branch.

The file says "no determinant identity is needed for h." At paper level this
is acceptable for defining h and its finiteness; the determinant/Ob3 step is
needed for the comparison to the q-pilot, and that comparison is supplied by
xi-f as a source step. For a first-principles proof this would be a gap.

## 5. Section 3: q-pilot input and SHE — ACCEPT

Fixed q-pilot input, not subject to Ind1/2/3: source xi-a/b.
IPL link by full poly-isomorphisms: source Rem3.11.1(iii).
SHE fixed 1-column expressibility and xi-e fixed value -|log q|: source
xi-b/xi-e.

Accurate paper-level citations.

## 6. Section 4: xi-f construction — ACCEPT paper-level, with interpretive caveat

The file states:

    xi-f constitutes a construction of the pilot-object log-volume of the
    input data, namely -|log q|;
    source qualifies: 'perhaps only up to some sort of approximation, as a
    result of various indeterminacies';
    here this means -|log q| is one of the possible pilot-object log-volumes,
    up to Ind1/2/3.

This is a coherent reading of xi-e/xi-f: the source's construction is a
construction of the input log-volume up to the indeterminacies that define R.
The inclusion -|log q| in R_{<= -|log Theta|} is then the source's formal
conclusion (lines 10712-10715).

Caveat: the source does not explicitly say the approximation is exactly the
Ind1/2/3 quotient with zero numerical error. The paper-level proof may use the
source's own xi-f step, so this is acceptable as a source-level proof; it is
not an independent derivation of exactness.

The proof does not strengthen "log-volume construction" into "q-pilot object is
literally one of the output objects"; it says "one of the possible pilot-object
log-volumes." That is the correct weaker statement.

## 7. Section 5: inequality and C_Theta — ACCEPT conditional on xi-f

From the source inclusion -|log q| in R_{<= -|log Theta|}, the inequality and
C_Theta>=-1 follow formally (source lines 10712-10715). Correct.

## 8. Section 6: paper-level status — ACCEPT

The file explicitly says:

- it is a paper-level proof following xi-e/xi-f, not a first-principles
  derivation;
- the approximation is treated as the Ind1/2/3 indeterminacy quotient, not an
  additional numerical epsilon;
- expansion of Theorem3.11/Prop3.9/Remark3.9.5 is not attempted;
- P6_can follows from Cor3.12 for paper objects.

This scope statement is honest. ACCEPT as paper-level; not as first-principles.

One caveat: "P6_can follows from Cor3.12 for paper objects" is true only for
the paper target Q_can=-|log q|, h_can=-|log Theta|. It does not automatically
identify an independently defined C9 target with the paper objects; T_can
remains a separate object-identity issue (task-403). For the paper-level
review, this is acceptable because the target is defined as the paper objects.

## 9. Per-section verdict

| section | verdict | reason |
|---|---|---|
| 0 theorem | ACCEPT | matches source Cor3.12 |
| 1 setup | ACCEPT | Def3.8/Prop3.9 accurate |
| 2 multiradial/finiteness | ACCEPT with caveat | source citation; WLOG negative branch omitted; determinant step deferred to xi-f |
| 3 q-pilot/SHE | ACCEPT | source xi-a/b/e |
| 4 xi-f construction | ACCEPT paper-level | source's formal inclusion used; exactness of approximation is source-interpretive, not independently proved |
| 5 inequality | ACCEPT conditional | formal from xi-f |
| 6 paper-level status | ACCEPT | scope honest; P6_can paper-only |

## 10. Hidden-assumption/circularity check

- Hidden assumption: WLOG -|log Theta|<0 when finite; repairable by adding the
  trivial h>=0 branch.
- Hidden interpretation: "perhaps approximation" = Ind1/2/3 quotient. At
  paper level this is the source's xi-f step; at first-principles level it is
  an unproved exactness assertion.
- Determinant/Ob3 comparison: skipped in the NL proof; xi-f is used as the
  source result. Not circular at paper level; a gap at first-principles level.
- No circularity in the theorem-to-inequality inference.
- P6_can paper object identity: accepted as paper target; C9 target identity
  remains T_can.

## 11. Conclusion

The file is **accepted as a paper-level proof of Cor3.12** because it follows
the source's own Theorem3.11/xi-e/xi-f structure and explicitly disclaims
first-principles expansion. It is **not accepted as a first-principles proof**
and does not by itself prove an independently defined C9 P6_can target. The
remaining caveats are: the WLOG negative branch, the interpretive exactness of
"perhaps approximation," and the deferred determinant/Ob3 comparison. No
rewrite is made; no mixed/E3; no Lean/kernel closure.

target_accepted=false; P6 open.

## 12. Status

- Independent review only; no Lean/Project edits.
- Paper-level Cor3.12 proof accepted with caveats; first-principles/C9 target
  claim not accepted.
- target_accepted=false.
