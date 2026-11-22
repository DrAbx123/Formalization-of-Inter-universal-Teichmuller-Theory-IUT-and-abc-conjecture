# C9 review: paper-level Cor 3.12 xi-f semantics

Task: task-424. Date: 2026-10-25. Reviewer: transport.
Review only; no rewriting of the reviewed proof. No Lean; no mixed/E3;
no arbitrary. Only this file written. target_accepted=false.

## 0. Input reviewed

C9-COR312-PAPER-PROOF-20261025.md, 100 lines,
SHA256 91F6BD347D7BABA6854BCE81ED185A553F536D27615EA4356D2F50F0B818431B.

Source: IUT-III.txt SHA256 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.

Critical source lines:

- xi-d: lines 10641-10681;
- xi-e: lines 10682-10704;
- xi-f: lines 10705-10715;
- Cor3.12 statement: lines 10152-10180.

## 1. Overall verdict

The reviewed file is a faithful **paraphrase of the source's formal xi-f
assertion**. It is NOT a paper-level proof of xi-f, and it is not a
first-principles derivation of the membership.

The decisive issue is the question asked: does "constitutes a construction of
-|log q|" imply membership "-|log q| in R up to Ind"?

Answer:

- As a statement of what the source does, NO: the source's phrase
  "constitutes a construction ... [perhaps only up to some approximation, as a
  result of various indeterminacies] of the pilot-object log-volume ... namely
  -|log q|" is followed in xi-f by the explicit assertion that the inclusion
  -|log q| in R_{<= -|log Theta|} follows formally. The file correctly reports
  this source assertion.
- As a derivation from xi-e alone, YES IT IS AN OVERREAD: "construction of a
  value" is not a formal set-membership predicate, and xi-e alone only gives
  expressibility under the fixed-value condition. The membership is xi-f's
  separate formal conclusion, not a consequence of xi-e.

The file does label xi-f as a source step and says it does not derive it from
lower-level principles. To that extent it is honest. However, it also claims to
be a "paper-level proof" while omitting two source steps that xi-f depends on:

1. xi-d determinant/log-volume comparison (A2);
2. the closed loop/sQ3/sQ4/AND of Remark 3.9.5(ix) and Remark 3.12.2(fitw).

Consequently: ACCEPT as a semantic paraphrase of xi-f; REJECT as a paper-level
proof of Cor 3.12.

## 2. Per-step verdicts

### Setup and definitions (Section 1) — ACCEPT

The source objects (initial Theta-data, Hodge theaters, q-pilot/Theta-pilot,
packet+procession normalization) are correctly named. This is a summary, not
an independent construction. Accept as source paraphrase.

### Multiradial representation (Section 2, first paragraph) — PARTIAL

The file invokes Theorem3.11/Remark3.11.1 and Ind1/Ind2/Ind3 correctly at the
level of names. But it does not specify:

- Ind1 includes automorphisms of the procession of D^dagger-prime-strips, not
  only label/procession permutations;
- Ind2 is independent copies of Ism / order-2 automorphisms on direct summands
  of the j+1 tensor factors, not a generic tensor-factor action;
- Ind3 is upper semi-compatibility (inclusions/surjections).

For a paper-level proof these labels are acceptable as names, but the proof
never uses the actual definitions. Partial accept; no exactness claim.

### Hull and finiteness (Section 2, second/third paragraphs) — QUALIFY

The definition of H as the smallest lambda*O containing PI is source
(Remark3.9.5(i)). The compactness line is source (lines 10234-10237).

Problems:

- The source says one concludes finiteness from the compactness of
  1,circ U_{j,vQ} together with the log-volume definition. It does not spell
  out compactness of the hull H itself. The file says "for fixed C the index
  set is finite, so H is compact"; that is an additional inference, plausible
  but not written in the source.
- The statement "no determinant identity is needed for h" is true for the
  definition of h as hull log-volume, but false for the comparison with
  -|log q|: xi-d uses the determinant precisely to make the two quantities
  comparable. See the next point.

QUALIFY: h is defined, but its comparability with -|log q| is not established
in this section.

### Definition of R (Section 2, fourth paragraph) — REJECT as paper-level

The file defines R as the set of log-volumes of possible output data up to
Ind1/2/3, and R_{<=h} accordingly. This definition presupposes that the output
data have a well-defined normalized log-volume in the same scale as the
q-pilot. In the source, that is exactly what xi-d establishes via the
determinant operation:

    xi-d, lines 10654-10660: only by forming a suitable positive tensor power
    of the determinant ... and then applying the log-volume ... are we able to
    obtain completely comparable objects, namely R_{<= -|log(Theta)|} and
    -|log(q)|.

The reviewed file omits xi-d entirely. It defines R and -|log q| as if they
were already in the same scale. This is a missing source step, not a harmless
simplification: the output is a rank>1 arithmetic vector bundle/localization,
while the q-pilot is an arithmetic line bundle; without det^otimes M and the
O(-) normalization there is no comparison.

REJECT as paper-level proof at this point. Accept only if one adds xi-d as a
separate source input.

### q-pilot fixed and SHE (Section 3) — ACCEPT

The q-pilot is fixed and not subject to Ind1/2/3 (xi-a/b). SHE is the source
property of Remark3.11.1(iii), and xi-e is correctly quoted: expressibility
relative to the 1-column under the condition that the pilot-object log-volume
be the fixed value -|log q|. Accept.

### xi-f interpretation (Section 4, first two paragraphs) — ACCEPT as source paraphrase

The file quotes xi-f:

    the construction of output data possibilities constitutes a construction
    of the pilot-object log-volume of the input data, namely -|log q|;
    the source qualifies this as "perhaps only up to some sort of
    approximation, as a result of various indeterminacies".

This is exactly xi-f, lines 10705-10715. ACCEPT as source quotation.

### xi-f implication "therefore -|log q| in R" (Section 4, third paragraph) — ACCEPT ONLY AS SOURCE ASSERTION; REJECT AS DERIVATION

If one reads xi-f as the source does, the inclusion is asserted by the source:

    xi-f, lines 10712-10715: "The inclusion -|log(q)| in R_{<= -|log(Theta)|},
    hence also the inequality -|log(q)| <= -|log(Theta)| ... then follows
    formally."

So the membership is not a new overread by the file; it is the source's formal
conclusion.

However, the file's added semantic explanation is stronger than xi-e:

    "Here 'constitutes a construction of -|log q|' has the following source
    meaning: the construction of output possibilities produces -|log q| as one
    of the possible pilot-object log-volumes."

This "source meaning" is not a direct source sentence. It is an interpretation
of xi-f's "constitutes a construction" as set membership. The source's own
formal step is the inclusion; the interpretation is acceptable only because
the source asserts the inclusion immediately afterward. It is NOT derivable
from xi-e alone.

ACCEPT the conclusion as a source assertion; REJECT any claim that xi-e alone
implies it.

### "Perhaps approximation = Ind1/2/3" (Section 4/6) — REJECT exact

The source xi-f says:

    "perhaps only up to some sort of 'approximation', as a result of various
    indeterminacies"

It does not say "Ind1, Ind2, Ind3" at this point. The file identifies the
"various indeterminacies" with Ind1/2/3 (Section 4 line 68-69 and Section 6
line 92-93). This identification is not in the source text. It may be the
intended reading, but as an exact paper-level proof it is an unsupported
identification. The task-417 review already flagged the same conflation.

REJECT the exact identification; qualify as "various indeterminacies,
presumably including Ind1/2/3".

### Closed loop and sQ3/sQ4 (omitted) — REJECT as paper-level proof

xi-f is not an isolated sentence: it depends on the closed loop of
Remark3.9.5(ix) through sQ1, sQ2, sQ3, sQ4, and on the compatibility
properties cQ3/cQ4. The reviewed file does not mention sQ1-sQ4 or the closed
loop at all. It quotes xi-f as if it were a direct formal consequence of
xi-e.

This is a missing source step. ACCEPT xi-f as a quoted source conclusion;
REJECT the file as a paper-level proof of xi-f.

### Inequality (Section 5) — ACCEPT conditional

Given the source's asserted membership
-|log q| in R_{<= -|log Theta|}, the inequality and C_Theta >= -1 follow
trivially. ACCEPT as a conditional consequence of xi-f membership.

### "Thus Cor3.12 is proved at the paper level" (Section 6) — REJECT

The file itself says it does not derive xi-f from lower-level principles, and
that an independent expansion of Theorem3.11/Prop3.9/Remark3.9.5/xi-f is not
attempted. That is honest. But then the claim "Cor3.12 is proved at the paper
level" is too strong: the file omits xi-d (determinant/comparability) and the
closed loop (sQ3/sQ4/AND), both of which are parts of the source's proof.

It is a **paraphrase of the source's final xi-f step**, not a paper-level
proof of Cor3.12.

## 3. Summary table

| step | verdict | exact reason |
|---|---|---|
| Setup/definitions | ACCEPT | source objects correctly named |
| Theorem3.11 invocation | PARTIAL | names okay, Ind definitions not specified |
| Hull H definition | ACCEPT | Remark3.9.5(i) |
| Finiteness of h | QUALIFY | compactness source assertion 10234-10237 |
| R definition and scale | REJECT as paper proof | xi-d determinant/comparability omitted |
| q-pilot fixed / SHE / xi-e | ACCEPT | 10166-10172, 10682-10704 |
| xi-f quotation | ACCEPT | 10705-10715 |
| "construction => membership" | ACCEPT as source assertion | xi-f formal inclusion 10712-10715 |
| "construction => membership" as derivation from xi-e | REJECT | non-sequitur; membership is xi-f |
| "various indeterminacies = Ind1/2/3" | REJECT exact | source does not say Ind1/2/3 |
| closed loop sQ1-sQ4 | REJECT as omitted | Remark3.9.5(ix), cQ3/cQ4 |
| inequality | ACCEPT conditional | trivial from membership |
| paper-level Cor3.12 proof | REJECT | omits xi-d and closed loop |

## 4. Exact gaps

(G1) xi-d omitted. R is defined as a set of output log-volumes and -|log q| as
the q-pilot log-volume without the determinant/O(-) construction that makes
them comparable. Source xi-d, lines 10654-10660, explicitly says the
determinant is needed to obtain "completely comparable objects".

(G2) Closed loop omitted. xi-f's formal inclusion depends on the closed loop
through sQ1-sQ4 and cQ3/cQ4 (Remark3.9.5(ix), lines 8383-8405). The file quotes
the conclusion without the chain.

(G3) Indeterminacy identification. The source's "various indeterminacies" in
xi-f is not explicitly "Ind1/2/3". The file's identification is an
interpretation.

(G4) Finiteness/compactness. The source's compactness input is quoted but not
expanded; the hull compactness inference is not source-written.

(G5) No counterexample: no source-valid C with the file's steps true and
Cor3.12 false is known. The objection is proof structure/omitted source steps,
not falsity.

## 5. Recommendation

Accept the file as a **semantic paraphrase of xi-f** and as a faithful
statement of the source's formal inclusion (with the caveat that the inclusion
is the source's assertion, not a derivation from xi-e).

Reject it as a **paper-level proof of Cor 3.12**: it omits xi-d
(determinant/log-volume comparability) and the closed loop sQ1-sQ4/cQ3/cQ4,
and it identifies "various indeterminacies" with Ind1/2/3 without source
support.

No mixed/E3 profile, arbitrary data, or Lean edit was used.
target_accepted=false.
