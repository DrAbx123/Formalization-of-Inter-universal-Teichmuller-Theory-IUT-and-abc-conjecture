# C9 no-sorry report: C9QThetaValuesNamed

Task: task-479 (C9-NOSORRY-QTHETA-20261025). Owner: logdescent. Date: 2026-10-25. No-sorry audit/repair; no fake/axiom/toy. Only this file written as the task deliverable; target Lean file edited only to remove unprovable assertions. No mixed/E3.

## 0. Verdict

The target file tmp/sheaf/n8/closure/C9QThetaValuesNamed.lean originally had three theorem-level sorries:

    missing_q_source    : MissingQSource X
    missing_theta_source: MissingThetaSource (X := X) mu
    missing_values_source: MissingValuesSource (X := X) mu

None is provable from the existing source-valid declarations under the no-fake/no-toy constraint:
- MissingQSource: no source-valid GlobalLqDonor is constructed; the only formal inhabitant is the explicitly underconstrained constant donor, which is not the paper source readout.
- MissingThetaSource / MissingValuesSource: no P6Readout is constructed; P6Readout existence is the named obligation p6ReadoutExists_obligation, and under an archimedean native place the frozen P6Readout is actually refuted by P6AdmRedesign.frozenP6Readout_impossible_of_archimedean_at.

Therefore the three sorry theorems were removed, not replaced by fake proofs or axioms. The definitions MissingQSource, MissingThetaSource, MissingValuesSource are retained as the exact obstruction predicates, with comments pointing to the obstruction. The target file now compiles with 0 sorries and 0 axiom declarations.

Build:
    lean-serial env lean -j1 -R D:/lean C9QThetaValuesNamed.lean
    EXIT 0
    one unrelated linter warning: unused BorelSpace section variable in QNamed_eq_nativeScalar (no error).

Target file hash after repair:
    D129976DCEEEAFB796DD9F0D40336D45BED6B18DD9C290AF350579C53CA0DEA7
Lines after repair: 114; sorries: 0; axioms: 0.
Before repair: 104 lines, 3 theorem-level sorries.

Axiom audit of the remaining theorem QNamed_eq_nativeScalar (audit copy, EXIT 0):
    depends on axioms: [propext, Classical.choice, Quot.sound]
No sorryAx.

## 1. Why missing_q_source is not provable source-visibly

P6ChainA.GlobalLqDonor (P6ChainA.lean lines 60-63) requires a global readout function

    readout : P6ChainALocal X -> Real
    readout_eq_local : readout (p6ChainALocal X) = qPilotSignedLog X

No actual source readout function is constructed in the tree. P6ChainA declares the existence obligation as a named sorry:

    theorem globalLqDonor_nonempty (X) : Nonempty (GlobalLqDonor X) := by sorry

Using that imported sorry as a proof would not produce a no-sorry target; it would hide the same gap in an imported declaration. The only other inhabitant is P6GlobalLqDonorUnderconstrained.constantGlobalLqDonor, which is a constant formal readout. P6GlobalLqTargetCorrection explicitly records that this constant donor is underconstrained and is not source-correct. It would be fake/toy for the paper source object.

Exact obstruction: no source-valid global L_q framework readout; the function field is the missing donor. The target retains

    def MissingQSource : Prop := Nonempty (GlobalLqDonor X)

as the exact obstruction predicate; it does not assert it.

## 2. Why missing_theta_source and missing_values_source are not provable

P6L.P6Readout (P6L.lean lines 78-87) requires an actual global admissible region pair, finite support, procession weights/dimensions, and the exact global ellOut value. P6L declares the existence obligation as a named sorry:

    theorem p6ReadoutExists_obligation : Nonempty (P6Readout X mu) := by sorry

No actual P6Readout is constructed in production. C9QThetaValuesNamed.ThetaSourceObject and ValuesSourceObject are both abbreviations for P6L.P6Readout; ValuesNamed is the set of its ellOut images. Thus missing_theta_source and missing_values_source are the same missing source object, not two independent facts.

Stronger obstruction: P6AdmRedesign.frozenP6Readout_impossible_of_archimedean_at proves, under an archimedean native place and the stated normed/finite-dimensional/null-singleton hypotheses,

    not Nonempty (P6Readout (X := X) (mu := mu)).

So a universal assertion MissingThetaSource would be false in that regime, not merely unproved. The corrected RelaxedP6Readout exists, but it is a different target, not the frozen P6Readout required by this file.

Exact obstruction: no actual global P6Readout/ellOut donor; the frozen P6Readout is refuted at archimedean places. The target retains MissingThetaSource and MissingValuesSource as exact obstruction predicates and does not assert them.

## 3. What was changed

The target file was edited as follows:
- removed the theorem declarations missing_q_source, missing_theta_source, missing_values_source (the three sorry proofs);
- retained their Prop definitions MissingQSource, MissingThetaSource, MissingValuesSource as the exact obstruction statements;
- added comments at each definition explaining why no theorem is included and pointing to this report;
- did not add axioms, dummy inhabitants, singletons, constant donors, or arbitrary data.

The file still contains the source-facing definitions:
- QNamed from actual P6ChainAData and the theorem QNamed_eq_nativeScalar;
- ThetaNamed from an exact ThetaSourceObject (conditional on such an object);
- ValuesNamed as the set of ellOut images, not a singleton;
- the missing-source Prop definitions.

## 4. Compile/audit result

Source target: tmp/sheaf/n8/closure/C9QThetaValuesNamed.lean
- EXIT 0 with lean-serial.
- 0 target sorries.
- 0 target axiom declarations.
- Warning only: unused section variable BorelSpace in QNamed_eq_nativeScalar; this is a linter warning, not an error, and does not affect the no-sorry result.
- The remaining theorem QNamed_eq_nativeScalar depends only on propext, Classical.choice, Quot.sound; no sorryAx.

The imports P6ChainA and P6L still contain their own named sorries (globalLqDonor_nonempty, p6ReadoutExists_obligation), but the target file's remaining declarations do not use them. Those imported sorries are the exact source gaps documented above; they are not hidden in the target.

## 5. Classification

| Item | Status |
|---|---|
| target compiles | YES, EXIT 0 |
| target sorry count | 0 |
| target axiom declarations | 0 |
| fake/toy inhabitant added | NO |
| missing_q_source proved | NO; exact obstruction retained as Prop |
| missing_theta_source proved | NO; exact obstruction retained as Prop |
| missing_values_source proved | NO; exact obstruction retained as Prop |
| imported P6ChainA/P6L sorries | remain; documented source gaps |
| statement_compiles | true |
| proof_body_checked | true for remaining declarations |
| kernel_closed | true relative to standard axioms |
| target_accepted | false |

## 6. Exact obstruction summary

Q source: no source-valid GlobalLqDonor; only the named sorry obligation and the underconstrained constant donor exist.

Theta source: no actual P6Readout/global ellOut donor; the named p6ReadoutExists_obligation is open, and the frozen P6Readout is impossible at an archimedean native place under the cited hypotheses.

Values source: Values are the ellOut images of the same missing P6Readout donor; no independent source object exists.

These are the exact obstructions. Removing the three sorry theorems without fake replacements is the only no-sorry policy consistent with the existing declarations; the file retains the obstruction Props instead of asserting unproved existence.

## 7. Conclusion

C9QThetaValuesNamed is now no-sorry: 0 target sorries, 0 target axioms, EXIT 0. The three former sorries were not provable from source-valid declarations; they were removed and documented as exact obstruction predicates. No fake/axiom/toy inhabitant was introduced. The imported P6ChainA/P6L named sorries remain the exact source gaps.

Only this report file is the task deliverable; target Lean edited only for the no-sorry repair; no mixed/E3. target_accepted=false.
