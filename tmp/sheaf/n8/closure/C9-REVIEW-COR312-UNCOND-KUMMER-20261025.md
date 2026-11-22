# C9 independent review: unconditional Cor3.12 natural-language proof

Task: task-416. Reviewer: kummer. Date: 2026-10-25.
Review only; no rewrite; no Lean/Project edits; no mixed/E3.
Only this file written. target_accepted=false; P6 open.

## 0. Reviewed file

- C9-COR312-UNCONDITIONAL-NL-20261025.md, 196 lines,
  SHA256 ea6a43d734e5be920f2e4bfae6bb7aa2fbfe40507d88070d0ef36cc946f891f4.
- Source: IUT-III.txt, SHA256
  822e03da7e2a7402a3bb406d698bb3374401e3fb102058c80864d6c06139353d.

Claimed theorem: unconditional Corollary 3.12 for every admissible initial
Theta-data: -|log Theta| in R, -|log Theta| >= -|log q|, and C_Theta >= -1.

## 1. Verdict

**REJECT the file as a self-contained unconditional natural-language proof
of Corollary 3.12.** Accept the theorem statement as the source theorem, and
accept most source citations, but the proof has a load-bearing gap at the
exactness of the xi-f inclusion and an omitted WLOG branch.

Accept as source-level:

- the statement of Corollary 3.12 (IUT III lines 10152-10180);
- the q-pilot/Theta-pilot definitions (Def3.8(i));
- the IPL/SHE/APT properties (Remark3.11.1(ii)-(iv));
- the hull/determinant/log-volume framework (Remark3.9.5, Prop3.9);
- the formal xi-f inclusion as a source conclusion.

Reject:

- Section 3 finiteness/negative WLOG is not handled: the source proof assumes
  -|log Theta|<0 whenever finite, with the opposite case trivial; the NL proof
  does not state or handle the case -|log Theta|>=0.
- Section 5 exactness: the source explicitly writes "perhaps only up to some
  sort of approximation, as a result of various indeterminacies" (lines
  10708-10710). The NL proof asserts the approximation is "precisely the
  indeterminacy quotient ... not an additional numerical error" without a
  source theorem that the quotient is exact. This is an unjustified exactness
  step.
- Section 5 "the closed loop exhibits the q-pilot object as one of the possible
  output data": the source gives a construction of the q-pilot log-volume up to
  indeterminacies, not an object-membership statement. The proof strengthens
  the source.
- Section 8 unconditionality: because Section 3's WLOG branch and Section 5's
  approximation exactness are not handled, the proof does not establish the
  theorem unconditionally as written.

## 2. Section-by-section review

### Section 0 (theorem statement): ACCEPT as source

IUT III lines 10152-10180 state Corollary 3.12 under the situation of Theorem
3.11: -|log Theta| in R, -|log Theta| >= -|log q|, C_Theta >= -1. The NL
statement is the source statement. Accept.

Caveat: the theorem's proof begins with the WLOG assumption
-|log Theta|<0 whenever finite (lines 10181-10185); the NL file omits this.

### Section 1 (setup): ACCEPT

Def3.8(i) q-pilot from q_v up to torsion; Def3.8(ii) LGP-link full
poly-isomorphism; packet+procession normalization from Prop3.9. These are
accurate source uses.

### Section 2 (Theorem3.11/Remark3.11.1): ACCEPT as citation, but not a proof

The file states IPL, SHE, APT, HIS and Ind1/2/3. These are the content of
Theorem3.11/Remark3.11.1; the citations are accurate.

However, the file does not prove Theorem3.11 or verify all its hypotheses
(e.g., a single LGP-link, sign conditions of Remark2.4.2, compactness of
1,circ U_{j,vQ}). For a natural-language reproduction of Cor3.12 this is
acceptable as source citation, but it is not a no-black-box expansion of
Theorem3.11. The task's "check unjustified use" flags this as under-expanded,
not false.

### Section 3 (hull and finiteness): ACCEPT with correction

- Remark3.9.5(i) hull definition: correct.
- Ob1-Ob2 arithmetic vector bundles/hulls: correct.
- Ob3-3 determinant may be omitted for log-volumes: correct (IUT III lines
  7846-7855).
- Finiteness: source lines 10234-10237 derive finiteness from compactness and
  log-volume; correct.

Correction/gap: source then says "hence negative [by our assumption at the
beginning]" because it assumed -|log Theta|<0 when finite. The NL file says
only "h finite" and does not handle the WLOG branch. The theorem is still true
(if -|log Theta|>=0, the inequality is immediate), but the proof as written
omits a case. This is repairable, not fatal.

### Section 4 (fixed q-pilot/SHE): ACCEPT

- q-pilot input fixed, not subject to Ind1/2/3: source xi-a/b.
- IPL link to output: source Rem3.11.1(iii), task-372/384.
- SHE fixed 1-column expressibility: source xi-b/xi-e.

Accurate source use.

### Section 5 (closed loop, formal quotient, xi-f): REJECT as exact

This is the load-bearing section.

1. The sQ1/sQ2/sQ3/sQ4 chain is a correct summary of Remark3.9.5(viii)/(ix)
   and Remarks3.10.2. Accept as source-level.
2. The closed loop statement (Remark3.9.5(ix)) is correct: only a closed loop
   completes the projection of the Theta-intertwining onto the q-intertwining.
   Accept.
3. The claim that this loop "exhibits the q-pilot object as one of the possible
   output data of the multiradial algorithm" is stronger than the source. The
   source says the construction of output possibilities constitutes a
   construction of the pilot-object log-volume of the input, perhaps only up to
   approximation; it does not say the q-pilot object is literally one of the
   output possible images. The section should conclude a log-volume membership,
   not object membership.
4. The exactness claim: source lines 10708-10710 explicitly say "perhaps only
   up to some sort of approximation, as a result of various indeterminacies".
   The NL file line 148-151 says the approximation is "precisely the
   indeterminacy quotient ... not an additional numerical error". This is an
   interpretation, not a source theorem. The formal quotient/realified
   semi-simplification (Ob9-1) does not by itself prove that the approximation
   is exact; it only says the indeterminacies are compatible with coarse
   log-volume invariants.
5. Therefore the inclusion -|log q| in R_{<=-|log Theta|} is not derived
   exactly in the NL proof; it is a source conclusion (xi-f) asserted after an
   unproved exactness step.

Verdict: REJECT as exact. Accept only conditional on an additional source
theorem/argument that the "perhaps approximation" is exact for the
packet+procession log-volume, or with an explicit error term.

### Section 6 (inequality): ACCEPT conditional

From -|log q| in R_{<=-|log Theta|}, the inequality follows formally; source
lines 10712-10715. Correct conditional on Section 5.

### Section 7 (summary): ACCEPT as source

Fig.3.8/xi-g tautological two-way computation; accurate.

### Section 8 (unconditionality): REJECT as written

The file claims no additional hypothesis. But:

- source proof uses the WLOG assumption -|log Theta|<0 whenever finite; the
  NL proof omits the opposite case;
- Section 5 exactness gap means the proof is conditional on an exactness
  interpretation of the approximation;
- Theorem3.11/Remark3.9.5 are cited rather than fully expanded, so the
  "unconditional" claim is only source-conditional.

The source theorem is unconditional, but this NL reproduction does not prove
it unconditionally as written.

## 3. Hidden assumptions / circularity

1. Hidden WLOG: -|log Theta|<0 when finite (source line 10183); omitted.
2. Hidden exactness: "perhaps only up to approximation" treated as exact
   indeterminacy quotient; no source proof.
3. Object-vs-log-volume strengthening: "closed loop exhibits q-pilot object
   as output" vs source log-volume construction.
4. Under-expanded Theorem3.11 hypotheses (sign conditions, compactness,
   single LGP-link) are not checked.
5. No circularity in the source-level tautological comparison itself, but the
   NL proof's Section 5 uses the q-pilot input to conclude q-pilot membership,
   which is precisely the xi-f content; without the source citation it would
   be circular.

## 4. Per-section verdict

| section | verdict | reason |
|---|---|---|
| 0 theorem | ACCEPT source | exact Cor3.12 statement |
| 1 setup | ACCEPT | Def3.8/Prop3.9 accurate |
| 2 Theorem3.11 | ACCEPT citation, under-expanded | not a no-black-box proof; hypotheses not checked |
| 3 hull/finiteness | ACCEPT with correction | source finiteness; WLOG negative branch omitted |
| 4 q-pilot/SHE | ACCEPT | source xi-a/b/e |
| 5 closed loop/xi-f | REJECT as exact | "perhaps approximation" treated as exact; object/log-volume strengthening |
| 6 inequality | ACCEPT conditional | formal from inclusion |
| 7 summary | ACCEPT source | Fig3.8 tautology |
| 8 unconditionality | REJECT as written | WLOG + approximation exactness unhandled |

## 5. Conclusion

The file correctly states the source Corollary 3.12 and accurately summarizes
the main source steps A1/IPL/hull/fixed q-pilot/SHE/closed loop. It is not,
however, a self-contained unconditional natural-language proof. The critical
xi-f inclusion is derived by interpreting the source's "perhaps only up to
some sort of approximation" as exact indeterminacy quotient, which the source
does not assert; and the source's WLOG -|log Theta|<0 branch is omitted. The
closed-loop statement is strengthened from a log-volume construction to an
object-membership claim. Therefore accept the theorem as a source theorem,
but reject the file as a complete unconditional proof.

No rewrite; no mixed/E3; no Lean/kernel closure; target_accepted=false;
P6 open.

## 6. Status

- Independent review only; no Lean/Project edits.
- Cor3.12 statement accepted; proof rejected as self-contained unconditional.
- Exact gaps: WLOG negative branch; approximation exactness; object-vs-log-volume.
- target_accepted=false.
