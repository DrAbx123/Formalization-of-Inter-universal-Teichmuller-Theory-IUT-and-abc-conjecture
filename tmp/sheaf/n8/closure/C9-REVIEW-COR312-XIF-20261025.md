# C9 review: Cor3.12 xi-f approximation / unconditionality

Task: task-421. Reviewer: qside. Date: 2026-10-25.
Review only: accept/reject per step with exact reasons. No rewrite, no new
proof, no Lean, no Project/target edits, no mixed/E3; only this file written.

## 0. Reviewed material

Source:
- IUT-III.txt SHA256
  822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D,
  Corollary 3.12 lines 10152-10180; proof Step (xi-e)-(xi-f) lines
  10682-10715; Step (xi-g) lines 10716-10720.

C9 claims:
- C9-P6-CAN-NATURAL-PROOF-20261025.md
  SHA256 E78BAD81B1ABE4CD365D77391888C7B4DC74A3B3CC4E5FC83E8F21EB7B58A1C9:
  claims a COMPLETE natural-language proof of P6_can; A3 is claimed exact
  via a formal quotient/closed loop (its Step (1)-(5)).
- C9-CAN-A3-CLOSEOUT-20261025.md
  SHA256 BAAC9B45E0BEC5A837C0E8F743A5708A5600A840392094A272140508E5B45B94:
  claims the "approximation" is not a numerical epsilon but the Ind1/2/3
  quotient.
- C9-CAN-A3-CLOSED-LOOP-20261025.md
  SHA256 4BAA76F206FC9CD526B470B992F33E53611C88518280F37B771BEC363F5C89EC:
  claims the closed-loop/subquotient AND yields exact membership; CL1-CL3
  remain.
- C9-CAN-A23-AUDIT-20261025.md
  SHA256 266764A6F6CF77E7E035F489C8BE8052225D8C9DA9B17B4C76E6479673F8A761:
  independent audit marks A3-L2/L3/I4/I5 open/approximate.

## 1. Summary verdict

ACCEPT:
- The source text and logical structure of xi-e.
- The source's asserted implication in xi-f, as a source-level assertion.
- The conditional statement: exact membership Q_can in R_{<=h_can} plus
  Cor3.12 implies Q_can<=h_can.
- The interpretation that the approximation qualifier is connected to
  Ind1/2/3, as a plausible source reading.

REJECT:
- The claim that xi-f gives an exact, unconditioned set membership
  Q_can in R_{<=h_can}.
- The claim that the "perhaps only up to some sort of approximation" phrase
  has been eliminated or is harmless by definition.
- The claim that the C9-P6-CAN-NATURAL-PROOF is a COMPLETE proof of
  unconditional P6_can.
- Any signed-epsilon-free conversion from "approximately constructed" to
  "exactly in R".

The correct status is: Cor3.12 remains a source theorem/assertion; the C9
natural-language proof of exact xi-f membership is conditional on a source
compatibility step that is not expanded. P6 remains open.

## 2. Per-step review of xi-e / xi-f

### Step E1. Fixed q-pilot input and its log-volume

Source (xi-e, lines 10682-10687): the relationship between the pilot-object
log-volume -|log(q)| and the input F^Vdash x mu-prime-strip is prescribed by
the 1-column arithmetic holomorphic structure.

Verdict: ACCEPT. This is a definitional/source-input statement; it is the
same A1 fixed/coric q-pilot input. No numerical approximation is involved.

### Step E2. SHE condition

Source (xi-e, lines 10688-10695): "expressibility relative to the arithmetic
holomorphic structure in the 1-column" [SHE] amounts to expressibility via
operations valid/executable even under the condition that the pilot-object
log-volume associated to the input data be equal to the fixed value
-|log(q)|.

Verdict: ACCEPT as the source definition of SHE. Note the word "condition":
this is a condition under which the construction is made, not yet a proof
that the fixed value is an exact output.

### Step E3. Output set linked to the q-pilot log-volume

Source (xi-e, lines 10696-10704): the multiradial algorithm followed by
holomorphic hull and log-volume yields a collection of possible log-volumes
of output data R_{<=-|log(Theta)|} that are linked via F^Vdash-prime-strip
isomorphisms to -|log(q)|.

Verdict: ACCEPT as a source assertion. It establishes a link/comparability,
not exact membership of the real number -|log(q)| in the set of possible
output log-volumes. The link is at the level of F^Vdash-prime-strips, not at
the level of real numbers.

### Step F1. The approximation qualifier

Source (xi-f, lines 10705-10711):
"the construction of the subset R_{<=-|log(Theta)|} ... is subject to the
condition that this construction of output data possibilities constitutes,
in particular, a construction [perhaps only up to some sort of
'approximation', as a result of various indeterminacies] of the pilot-object
log-volume of the input data ..., namely, -|log(q)| in R."

Verdict: ACCEPT the text; REJECT the claim that this qualifier can be ignored.
The phrase is attached to the construction of the output possibilities. It is
not a statement of an exact equality. Two readings are possible:

(i) Semantic/indeterminacy reading: "up to approximation" means up to
    Ind1/2/3, and at the log-volume quotient the fixed value is exact.
(ii) Numerical reading: the fixed real value is only approximated by an
    output value; an error epsilon is needed.

The source does not explicitly choose between (i) and (ii), and does not give
an epsilon or a sign. Therefore the qualifier is a real source gap, not
decorative wording.

### Step F2. Construction constitutes construction of the input value

Source: same sentence, "constitutes ... a construction ... of the
pilot-object log-volume of the input data, namely, -|log(q)| in R."

Verdict: ACCEPT only as a source assertion of the intended semantics.
REJECT as an exact derived equality. "Constitutes a construction of" is weaker
than "equals" and weaker than "is an element of the output set". The source
does not display a map from the input q-pilot value to an output log-volume
element.

### Step F3. Inclusion -|log(q)| in R_{<=-|log(Theta)|}

Source (xi-f, lines 10711-10715): "The inclusion -|log(q)| in
R_{<=-|log(Theta)|}, hence also the inequality ..., then follows formally."

Verdict: REJECT as an exact, unconditioned derivation from the preceding
steps. Reasons:

1. The preceding construction is qualified by "perhaps only up to some sort
   of approximation".
2. No exact output element equal to -|log(q)| is constructed.
3. No signed error epsilon is stated with, e.g.,
       -|log(q)| + epsilon in R_{<=h_can},  epsilon <= 0
   or with a proved bound.
4. The link is via F^Vdash-prime-strip isomorphisms; the source does not
   prove that the normalized log-volume of the linked prime-strip equals the
   fixed real number exactly.
5. "Follows formally" is a source assertion, not an expansion. The inclusion
   is exactly the gap, not a consequence of the definitions.

ACCEPT the inclusion only as a source-level assertion conditional on reading
(i) plus an unexpanded compatibility statement.

### Step F4. Inequality -|log(q)| <= -|log(Theta)|

Verdict: ACCEPT as a conditional consequence of exact membership F3. If
-|log(q)| is in R_{<=-|log(Theta)|} = {lambda | lambda <= -|log(Theta)|},
then the inequality is immediate by definition. REJECT as unconditional from
F1-F2 alone.

### Step F5. C_Theta >= -1

Verdict: ACCEPT as algebra conditional on F4 and |log(q)|>0. REJECT as
unconditional, for the same reason.

### Step G. xi-g "two tautologically equivalent computations"

Source (xi-g, lines 10716-10720): the algorithm followed by hull and
log-volume yields two tautologically equivalent ways to compute the q-pilot
log-volume.

Verdict: ACCEPT as the source's summary/intention. It is not an independent
proof of exact membership; it restates the construction-computation. The
tautology is at the level of the intended object, not at the level of an
expanded set-theoretic map.

## 3. Review of the C9 "formal quotient" resolution

C9-CAN-A3-CLOSEOUT argues:
(1) the approximation in xi-f is not a numerical epsilon but the Ind1/2/3
    indeterminacy quotient;
(2) fitw gives
       (q-itw) => (q-itw) AND (Theta-itw/indets) => (Theta-itw/indets);
(3) hence exact membership Q_can in R_{<=h_can}.

Review:

- ACCEPT (1) as a plausible source interpretation. The phrase "as a result of
  various indeterminacies" supports it.
- ACCEPT (2) as a source-asserted logical relation.
- REJECT (3) as an exact derived conclusion. The following are still missing:
  * the subquotient operations of Remark3.9.5(viii) and the AND of (citw) are
    cited, not expanded;
  * the fitw relation is about intertwinings up to Ind1/2/3, not about a real
    number being an element of the set R of possible output log-volumes;
  * Ind3 is an inequality from above, not an exact quotient equality;
  * no proof that normalized log-volume is constant/invariant along the
    quotient in the direction needed for exact membership.
So the formal-quotient resolution is a conditional interpretation, not an
elimination of the xi-f gap.

## 4. Review of the closed-loop / subquotient expansion

C9-CAN-A3-CLOSED-LOOP claims:
- closed loop q -> Theta -> sQ1/sQ2 -> sQ3/sQ4 -> q;
- closed loop yields a prime-strip simultaneously equipped with both
  intertwinings;
- apply log-volume: Q_can in R_{<=h_can}.

Review:

- ACCEPT the source references: Remark3.9.5(viii),(ix); Step (xi-d)-(xi-f);
  Remark3.12.2(citw),(fitw).
- ACCEPT the closed-loop is the intended source construction.
- REJECT exact membership as proved. Its own residual gaps CL1-CL3 remain:
  CL1 formal quotient indeterminacies not expanded as exact quotient
  operations;
  CL2 sQ3/sQ4 compatibility with log-Kummer is source-asserted;
  CL3 subquotient AND identification is source-asserted, not a set-theoretic
  map.
These are exactly the steps needed to convert the closed loop into the real
inclusion. Without them, the closed-loop argument is a schema.

## 5. Review of the claim of a COMPLETE natural-language proof

C9-P6-CAN-NATURAL-PROOF claims (line 3 "COMPLETE", section 6 theorem) that
P6_can is proved for every admissible C.

Verdict: REJECT the COMPLETE/unconditional claim.

Reasons:
- A2 (determinant/log-volume identity) remains a source schema with
  undisplayed E_H, M, O(-), degree=log-volume, weights, hull approximant, and
  vertical-shift details.
- A3 (xi-f exact membership) is not an exact derivation; the source says
  "perhaps only up to some sort of approximation" and gives no signed epsilon.
- T_can (C9Hull/C9QPilot identity with source objects) is definitional only
  under the paper-target convention; as a theorem about abstract C9 objects it
  is an object-identity gap.
- The proof's A3 Step (4) treats the AND as "purely formal", but the source
  does not display the subquotient operations that would make it formal at
  the log-volume readout.

ACCEPT only:
  A1 + A2(exact) + A3(exact) + T_can  =>  P6_can.
This is a valid conditional implication, not a completed proof.

## 6. Review of "unconditionality"

The source Cor3.12 is a theorem under the hypotheses of Theorem 3.11, not an
absolute statement. For the C9 P6 claim, "unconditional" would require all of:

(U1) exact A2 determinant/log-volume identity;
(U2) exact A3 membership or signed epsilon;
(U3) exact T_can object identification;
(U4) no unproved normalization/arch factor.

None of U1-U3 is expanded in the reviewed C9 NL proof. U4 is handled in the
canonical target but the arch/normalized variant has its own h_inf issue.
Therefore:

- Cor3.12 as a source theorem: ACCEPT.
- xi-f exact inclusion as a source assertion: ACCEPT conditionally.
- xi-f exact inclusion as an expanded natural-language proof: REJECT.
- Unconditional P6_can: REJECT.
- Conditional P6_can schema: ACCEPT.

## 7. Per-step decision table

| step | claim | verdict | reason |
|---|---|---|---|
| E1 | q-pilot fixed input/log-volume | ACCEPT | source definition/source input |
| E2 | SHE fixed-value condition | ACCEPT | source definition |
| E3 | output set linked to q-pilot | ACCEPT | source assertion; link not real equality |
| F1 | construction up to approximation | ACCEPT text / REJECT deletion | qualifier is real; no exact equality |
| F2 | constitutes construction of input value | ACCEPT only as source assertion | not an exact element map |
| F3 | Q_can in R_{<=h_can} | REJECT unconditional | approximation unresolved; no epsilon/sign; formal quotient not expanded |
| F4 | Q_can<=h_can | ACCEPT conditional on F3 | immediate from definition |
| F5 | C_Theta>=-1 | ACCEPT conditional | algebra from F4 |
| G | tautological two computations | ACCEPT as source summary | not independent proof |
| A3 closeout | approximation=Ind quotient/exact membership | REJECT as proved | fitw/subquotient/Ind3 compatibility unexpanded |
| Final P6_can | unconditional/completed proof | REJECT | A2/A3/T_can gaps |

## 8. Conclusion

The review accepts Corollary 3.12 and the xi-e setup. It accepts xi-f as the
source's intended construction-computation, and accepts the implication
"exact membership => P6_can". It rejects the claim that xi-f's approximation
qualifier has been eliminated or that exact membership follows
unconditionally. The C9 "formal quotient" and "closed loop" files are
conditional interpretations, not expansions; their own CL1-CL3 and
fitw/subquotient gaps remain. The C9-P6-CAN-NATURAL-PROOF is not a COMPLETE
proof of unconditional P6_can; it is a conditional schema.

No Lean, no mixed/E3, no arbitrary data. target_accepted=false; P6 open.

## 9. Sources

- IUT III Cor3.12 / xi-e-f: sources/IUT-III.txt SHA256
  822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.
- C9-P6-CAN-NATURAL-PROOF-20261025.md (COMPLETE claim) SHA256
  E78BAD81B1ABE4CD365D77391888C7B4DC74A3B3CC4E5FC83E8F21EB7B58A1C9.
- C9-CAN-A3-CLOSEOUT-20261025.md SHA256
  BAAC9B45E0BEC5A837C0E8F743A5708A5600A840392094A272140508E5B45B94.
- C9-CAN-A3-CLOSED-LOOP-20261025.md SHA256
  4BAA76F206FC9CD526B470B992F33E53611C88518280F37B771BEC363F5C89EC.
- C9-CAN-A23-AUDIT-20261025.md SHA256
  266764A6F6CF77E7E035F489C8BE8052225D8C9DA9B17B4C76E6479673F8A761.
