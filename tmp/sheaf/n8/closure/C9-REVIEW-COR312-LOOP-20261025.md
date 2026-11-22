# C9 review: Cor3.12 Section 5 closed loop / sQ3 / sQ4

Task: task-420 (C9-REVIEW-COR312-LOOP-20261025). Owner: logdescent. Date: 2026-10-25. Review only; no rewrite; uniform scope; no mixed/E3; only this file written; no Lean/Project/target/other-owner edits; no arbitrary. P6 open.

Reviewed: C9-COR312-UNCONDITIONAL-NL-20261025.md, Section 5 (closed loop and formal quotient, lines 115-158), with its Section 2-4 inputs; cross-checked against C9-CAN-A3-CLOSED-LOOP-20261025.md, C9-CAN-A3-CLOSED-LOOP-DERIVED-20261025.md, C9-CAN-A3-COMPATIBILITY-DERIVATION-20261025.md, C9-CAN-A3-SUBQUOTIENT-EXPANDED-20261025.md.

Source anchors:
- closed loop: IUT III Remark 3.9.5(viii),(ix), lines 8383-8405; non-closed loop warning lines 8406-8431.
- Ob9/Ob9-1 formal quotient: lines 8128-8161 (approx; exact local line range per C9 subquotient doc).
- cQ3/cQ4: lines 8264-8366; Ob7/Ob8 lines 7961-8127.
- sQ1/sQ2: Remark3.10.2; sQ3/sQ4: Remark3.9.5(viii),(ix).
- xi-f inclusion: lines 10705-10715; xi-e lines 10682-10704.

## 0. Verdict

Section 5 is NOT an unconditional derivation. It is a source-citation chain with two asserted bridges:

1. The closed loop through sQ1-sQ4 is **asserted in the source**, not derived from cQ3/cQ4 or from the individual poly-isomorphisms. The source says the chain "forms a closed loop ... up to the introduction of the formal quotient indeterminacies" (lines 8403-8405). cQ3 and cQ4 are compatibility properties of sQ3/sQ4; cQ3+cQ4 do NOT imply the composite closed loop (C9-CAN-A3-COMPATIBILITY-DERIVATION, lines 92-98). ACCEPT as source assertion; REJECT any derivation claim.
2. The xi-f inclusion is **also asserted separately in the source** (xi-e/xi-f), not derived from the closed loop. The unconditional NL's sentence "the closed loop exhibits the q-pilot object as one of the possible output data" (lines 155-158) is an added semantic bridge: the closed loop is a prime-strip simultaneously equipped with both intertwinings; it does not, by itself, exhibit the q-pilot object as an output data element of the multiradial algorithm. ACCEPT the xi-f inclusion only as the source's separate formal conclusion; REJECT its derivation from the closed loop.
3. The identification of the xi-f "perhaps only up to some sort of approximation" with the Ob9-1 formal quotient is a plausible source-level interpretation, but it is not an exact source theorem. ACCEPT as interpretation; REJECT as a proved identity.
4. cQ3/cQ4 are source-asserted; the C9 natural-language derivations are plausible but not a line-by-line source proof. ACCEPT conditionally; do not claim full derivation.
5. Ob9-1 "no effect on comparability" is source-asserted. ACCEPT at source level; the exact quotient/equality of the set of possible output log-volumes is not expanded, so it cannot be used to convert the closed loop into exact set membership without xi-f.

Therefore Corollary 3.12 remains a source-asserted theorem at this step; the unconditional NL proof does not derive the loop or xi-f from more basic data. No numerical error is involved; the gaps are semantic/source-assertion gaps.

## 1. Step review

### Step 1: sQ1/sQ2 poly-isomorphisms

Claim: sQ1 (Kummer-detachment) and sQ2 (Galois evaluation) of Remark3.10.2 are poly-isomorphisms of F^⊩×μ-prime-strips composing with the LGP-link.

Source: Remark3.9.5(ix) lines 8396-8399 explicitly says the chain passes through the poly-isomorphisms of F^⊩×μ-prime-strips induced by sQ1, sQ2; Remark3.10.2 supplies the diagram.

Verdict: ACCEPT as source citation. This is not the loop itself; it is one segment.

### Step 2: sQ3/sQ4 compatibility (cQ3/cQ4)

Claim: sQ3 (positive tensor powers of determinants of hulls plus the set-theoretic ⊼-formalism) and sQ4 (vertical-shift adjustment via log-Kummer) satisfy compatibility cQ3/cQ4 with the F^⊣×μ-prime-strip data.

Source: Remark3.9.5(ix) lines 8385-8402 cites cQ3/cQ4 and says sQ3/sQ4 "satisfy the compatibility property with the log-Kummer correspondence"; Ob7/Ob8 and cQ3/cQ4 lines 7961-8366.

Verdict: ACCEPT as source assertion; CONDITIONAL on the C9 natural-language derivations. The derivations in C9-CAN-A3-COMPATIBILITY-DERIVATION are plausible but not a line-by-line source proof; cQ3/cQ4 are compatibility properties, not the closed loop.

### Step 3: closed loop

Claim: the chain
  q-pilot codomain -> LGP-link to domain -> sQ1/sQ2 -> sQ3/sQ4 -> back to q-pilot
forms a closed loop; only a closed loop completes the projection of the Theta-intertwining onto the q-intertwining.

Source: Remark3.9.5(ix) lines 8383-8405: "It is precisely by passing through (sQ3), (sQ4) ... that the chain ... forms a closed loop, i.e., up to the introduction of the 'formal quotient indeterminacies' discussed in (cQ3), (cQ4) [cf. also (Ob9-1)]." Lines 8406-8431: a non-closed loop yields no nontrivial conclusion; omitting sQ3/sQ4 breaks the loop.

Verdict: ACCEPT as source ASSERTION; REJECT as derived from cQ3/cQ4.
- The source asserts the loop's closure; it does not derive it from the compatibility properties cQ3/cQ4 alone. C9-CAN-A3-COMPATIBILITY-DERIVATION lines 8-13 and 92-98 explicitly state: cQ3+cQ4 do NOT imply the composite closed loop; Remark3.9.5(ix) asserts the loop separately.
- The closure is "up to formal quotient indeterminacies"; this is not an exact identity of objects. The source uses the loop to complete a projection, not to produce a set-theoretic equality of output data.
- The unconditional NL cites "By Remark3.9.5(ix)" for closure; that citation is correct. But its conclusion that the loop is a construction of the **possible output data** is a separate semantic step (see Step 4).

### Step 4: Ob9-1 formal quotient

Claim: the formal indeterminacies (tensor-power-twist, ⊼, log-link iterates) are treated by Ob9-1; they have no effect on comparability; the realified semi-simplification induces a natural bijection between log-volumes of hulls in domain/codomain.

Source: Ob9-1 lines 8145-8161; Ob9 lines 8128-8144; source says these formal indeterminacies have no effect on comparability of the objects obtained in Ob5.

Verdict: ACCEPT source assertion "no effect on comparability"; CONDITIONAL/REJECT exact quotient identity.
- The source does not state an exact quotient operation that would allow one to replace "up to indeterminacies" by an equality of possible output log-volume sets.
- The unconditional NL identifies the xi-f "perhaps only up to some sort of approximation" with this Ob9-1 quotient (lines 148-151). That identification is consistent with the source wording but is not a separately proved theorem. It may be used as the source's intended reading, not as an exact derived equality.
- The "natural bijection between log-volumes of hulls in domain/codomain" is a source-level compatibility, not a proof that the q-pilot value is an element of the output set. That membership is xi-f, not Ob9-1.

### Step 5: xi-f inclusion

Claim: the closed loop exhibits the q-pilot object as one of the possible output data of the multiradial algorithm; its log-volume is -|log q|; R_{<= -|log(Theta)|} is the set of possible output log-volumes bounded by -|log(Theta)|; hence -|log q| in R_{<= -|log(Theta)|}.

Source: xi-f lines 10705-10715: the construction of R_{<= -|log(Theta)|} is subject to the condition that this construction constitutes a construction (perhaps only up to approximation) of the pilot-object log-volume of the input, namely -|log q|; the inclusion then follows formally.

Verdict: ACCEPT the source's xi-f inclusion as a **separate source assertion**; REJECT its derivation from the closed loop alone.
- The closed loop is a prime-strip simultaneously equipped with the Theta-intertwining (up to Ind1/2/3) and the q-intertwining (lines 8417-8424). That is not the same statement as "the q-pilot object is one of the possible output data of the multiradial algorithm." The q-pilot object is the fixed input/codomain object; the output data are in 1,circU.
- To derive membership from the closed loop one would need an additional theorem: the closed-loop prime-strip's q-pilot portion is an output data element, not merely the loop's endpoint. The source does not state this in Remark3.9.5(ix); the membership is asserted in xi-f via the construction/constitution sentence.
- The unconditional NL's "Indeed..." sentence (lines 155-158) is therefore a semantic bridge, not a source derivation. It may be accepted as the intended reading of xi-f, but it cannot be labeled derived.
- The parenthetical approximation means the membership is source-asserted "perhaps up to approximation"; the unconditional NL removes the approximation by identifying it with the Ob9-1 quotient, which is not an exact source theorem.

## 2. What is accepted vs rejected

ACCEPTED:
- sQ1/sQ2 poly-isomorphism segment: source citation.
- sQ3/sQ4 compatibility cQ3/cQ4: source assertion, with C9 NL derivation conditional.
- Closed loop: source assertion (Remark3.9.5(ix)); closure up to formal quotient indeterminacies.
- Ob9-1 no effect on comparability: source assertion.
- xi-f inclusion: source assertion (separate from the loop).

REJECTED:
- "The closed loop is derived from cQ3/cQ4." False per compatibility derivation; the source asserts it separately.
- "The closed loop alone derives -|log q| in R_{<= -|log(Theta)|}." The source's xi-f membership is separate; the loop does not by itself exhibit q-pilot as an output data element.
- "The xi-f approximation is exactly the Ob9-1 quotient, with no residual gap." This is an interpretation, not an exact source theorem. It removes the approximation wording without proof.
- "Section 5 is an unconditional derivation." It is a source-citation chain with asserted bridges; it does not derive the loop or xi-f from the preceding data.

## 3. Exact gaps

G-loop: the closed loop is asserted in Remark3.9.5(ix), not derived; the source does not give a line-by-line proof from cQ3/cQ4. The loop is only up to formal quotient indeterminacies.
G-cQ: cQ3/cQ4 are compatibility properties; their NL derivations are plausible but conditional, and they do not imply the composite loop.
G-Ob9: the exact quotient action of Ob9-1 is not expanded; "no effect on comparability" is a source assertion, not an equality of possible log-volume sets.
G-xi-f: the membership -|log q| in R_{<= -|log(Theta)|} is asserted in xi-f, not derived from the loop. The approximation parenthetical is not quantified; identifying it with Ob9-1 is an interpretation.
G-derivation: the unconditional NL's "Indeed..." step is an added semantic bridge, not source text.

These are source-structure gaps, not numerical errors; no arbitrary epsilon or normalized surrogate is introduced.

## 4. Consequence for the unconditional NL proof

The Section 5 argument does not establish Corollary 3.12 as an unconditional **derivation**. It correctly cites the source's closed loop assertion and xi-f assertion, but:
- it does not derive the closed loop from cQ3/cQ4;
- it does not derive xi-f membership from the closed loop;
- it identifies the approximation with Ob9-1 without an exact quotient proof.

Therefore the unconditional proof is source-faithful as a **citation/schema**, but not a proof from more basic principles. It may be accepted as a source-level proof only if Remark3.9.5(ix) and xi-f are accepted as source assertions; it cannot be labeled an independent derivation. No Lean/formal closure follows from it.

No rewrite of the reviewed file; this is accept/reject. No mixed/E3; no Lean.

## 5. Verdict summary

| Step | Verdict |
|---|---|
| sQ1/sQ2 polyiso segment | ACCEPT source |
| sQ3/sQ4 cQ3/cQ4 | ACCEPT source-asserted; derivation conditional |
| Closed loop | ACCEPT source assertion; REJECT derivation from cQ3/cQ4 |
| Ob9-1 no effect on comparability | ACCEPT source assertion; exact quotient not proved |
| xi-f inclusion | ACCEPT source assertion; REJECT derivation from closed loop |
| Approximation = Ob9-1 quotient | INTERPRETATION, not exact source theorem |
| Section 5 unconditional proof | NOT ACCEPTED as derivation; source-citation schema |

Only C9-REVIEW-COR312-LOOP-20261025.md written. No Lean/Project edits. target_accepted=false; P6 open.
