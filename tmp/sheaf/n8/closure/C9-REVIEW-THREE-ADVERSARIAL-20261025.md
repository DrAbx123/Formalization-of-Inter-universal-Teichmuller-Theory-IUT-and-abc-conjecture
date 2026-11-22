# C9 adversarial review of C9Cor312ThreeAssumptions.lean

Task ID: task-465 / C9-REVIEW-THREE-ADVERSARIAL-20261025. Reviewer: primespine. Date: 2026-10-25.
Object: tmp/sheaf/n8/closure/C9Cor312ThreeAssumptions.lean (59 lines).
Source mapping claimed: C9-COR312-FROM-ASSUMPTIONS-20261025.md (A1=Theorem3.11, A2=Prop3.9, A3=Remark3.9.5).
Scope: independent adversarial review; no Lean/Project edits; no mixed/E3; only this file written.

## 0. Verdict

**REJECT the Lean artifact as a source-mapped proof of Cor3.12/C1.** The decisive defect is that C1 is a hidden field of `Theorem311Full`: line 18 assumes `qPilotOutput ∈ possibleOutputs`, which is exactly the output-membership statement to be proved. The theorem then extracts this field. In addition, `Prop39`/`Remark395` are arbitrary abstract carriers with no source identification, and `sourceThreeAssumptions` is an unconstrained axiom of existence. The target is not `Q_can <= h_can` with the paper objects; it is an abstract inequality `qLog <= h`.

The file is at most a conditional abstract lemma: if one assumes a set of outputs containing a q-pilot output, a log-volume function, and an upper bound, then the q-pilot log-volume is bounded. That is not Theorem3.11 + Prop3.9 + Remark3.9.5, and it is not C1/Cor3.12.

## 1. `Theorem311Full`: REJECT — hidden C1 and arbitrary carrier

Lines 13-18 define:

    Output : Type
    possibleOutputs : Set Output
    logVol : Output -> R
    qPilotOutput : Output
    qPilotOutput_mem : qPilotOutput in possibleOutputs.             (1.1)

Exact reasons:

1. **`qPilotOutput_mem` is C1.** C1 says the q-pilot value is realized by a possible output; line 18 literally assumes a q-pilot output belonging to the possible-output set. The theorem `cor312` then uses this field (line 44) to prove the inequality. This is circular at the level of the encoded assumptions.
2. **Not the source Theorem3.11.** Source Theorem3.11 provides a multiradial algorithm, IPL/SHE/APT, and Ind1/2/3. It does not provide a field saying the fixed q-pilot input rigidification is one of the possible outputs. The comment on lines 10-12 asserts this as 'Theorem3.11, full content needed here'; that is exactly the unproved xi-e/xi-f compatibility, not the theorem's content.
3. **Arbitrary carrier.** `Output` is any type, `possibleOutputs` any set, `logVol` any function to R. No BPS/F-prime-strip, no Theta-pilot/hull, no measure/normalization, no Ind1/2/3. This is not a source model; it is an abstract interface that can be instantiated arbitrarily.

## 2. `Prop39`: REJECT — target mismatch and no q-pilot object

Lines 21-23 define only `qLog : R` with `qLog = logVol qPilotOutput`.

Problems:

- No q-pilot object, BPS, global realified Frobenioid, packet normalization, or procession average. `qLog` is an arbitrary real, not `Q_can=-|log q|`.
- The identification of `qLog` with the paper q-pilot log-volume is absent. Calling this structure `Prop39` does not make it Proposition3.9.
- `qLog_eq` is definitional in the abstract model, not the source relation 'q-pilot log-volume is read on the q-pilot output'.

## 3. `Remark395`: PARTIAL/REJECT — h arbitrary and upper bound assumed

Lines 27-31 define `R = logVol '' possibleOutputs`, `h : R`, and `hull_upper : forall x in R, x <= h`.

Problems:

- `h` is an arbitrary real, not the procession-normalized hull log-volume `h_can=-|log Theta|`.
- `hull_upper` is assumed for all possible outputs, but the source Remark3.9.5 gives a hull construction; the relation must be proved from the hull/log-volume, not taken as a field of the remark.
- No identification of `R` with `R_{<=h_can}` or of the q-pilot value with `Q_can`. The abstract R is an image set of an arbitrary `logVol`, not the Cor3.12 possible-output log-volume set.

## 4. `cor312`: ACCEPT only as an abstract conditional lemma

Lines 41-45 prove: if `qLog` is the log-volume of a possible output and all possible log-volumes are <= h, then `qLog <= h`. The proof is correct.

But this is exactly the circular pattern: the first premise is line 18 (C1), the second is an abstract upper bound. As a source proof of Cor3.12 it is REJECT; as a trivial conditional lemma it is accepted.

## 5. `sourceThreeAssumptions`: REJECT — unconstrained axiom / axiom proliferation

Line 48: `axiom sourceThreeAssumptions : ThreeAssumptions`.

Problems:

1. **No source construction.** It asserts existence of an arbitrary `ThreeAssumptions` package. It does not construct A1/A2/A3 from initial Theta-data, Hodge theaters, BPS, or the source log-volume. The only imports are Mathlib; no IUT module is referenced.
2. **Arbitrary inhabitant.** Since `ThreeAssumptions` has fields for arbitrary types/sets/functions, the axiom can be satisfied by a degenerate model; it has no source semantics. This is worse than a sorry: it is an unconstrained existence axiom.
3. **Axiom proliferation/mislabeling.** The comment calls the three assumptions 'source axioms/inputs'; the axiom is not a source theorem. `#print axioms cor312_unconditional` will display `sourceThreeAssumptions` (plus any Mathlib classical axioms); that is not a kernel-checked source proof.

## 6. `cor312_unconditional`: REJECT — not unconditional, target mismatch

Lines 51-53 conclude the abstract inequality from the arbitrary axiom. The name 'unconditional' is misleading: it is conditional on `sourceThreeAssumptions` and on the hidden C1 field.

Target mismatch: the paper target is `Q_can=-|log q| <= h_can=-|log Theta|` with canonical packet+procession normalization. The Lean conclusion is `A.P39.qLog <= A.R395.h` for arbitrary `qLog,h`. No comparator/identification maps the Lean quantities to the paper quantities. Even if the abstract inequality is true, it does not establish Cor3.12/P6_can.

## 7. Additional hidden fields/assumptions

- `Theorem311Full.Output`/`possibleOutputs`/`logVol` arbitrary; no source model.
- `qPilotOutput` existence and membership (C1) hidden in A1.
- `Prop39.qLog` arbitrary; no q-pilot normalization or BPS.
- `Remark395.h` arbitrary; no hull construction, no Ind1/2/3, no Theta-pilot.
- `hull_upper` assumed rather than derived from hull/log-volume.
- `sourceThreeAssumptions` arbitrary existence axiom.

## 8. Accept/reject table

| component | verdict | reason |
|---|---|---|
| `Theorem311Full` | REJECT | hidden C1 in `qPilotOutput_mem`; arbitrary carrier; not source Thm3.11 |
| `Prop39` | REJECT | arbitrary qLog; no q-pilot/BPS/normalization; target mismatch |
| `Remark395` | REJECT/PARTIAL | h arbitrary; hull_upper assumed; no source hull |
| `cor312` | ACCEPT conditional only | valid trivial implication; circular as source proof |
| `sourceThreeAssumptions` | REJECT | unconstrained axiom; no source construction |
| `cor312_unconditional` | REJECT | conditional on axiom/hidden C1; target mismatch |

## 9. Final review verdict

**REJECT the Lean artifact.** It assumes C1 as a field, hides it inside a mislabeled 'Theorem3.11', uses arbitrary abstract carriers, adds an unconstrained existence axiom, and concludes an abstract inequality unrelated to the paper target. It is not a source-mapped proof of Cor3.12/C1 and must not be accepted as kernel closure. No Lean edits; no mixed/E3.

target_accepted=false; kernel_closed=false.
