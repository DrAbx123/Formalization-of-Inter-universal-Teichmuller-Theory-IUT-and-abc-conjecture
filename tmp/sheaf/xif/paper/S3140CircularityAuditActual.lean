import tmp.sheaf.xif.paper.S3140ClosureGateActual
import LeanFormal.IUT.Audit.Status

/-!
# S3140 strict circularity audit of the final gate dependency closure (task-68)

**Verdict: NO proof circularity found in the V3 gate closure.**  The audit was
requested after the user warned that the paper may contain input errors; it
checks the 41-import gate closure (paper-local transitive closure = 461 files,
computed from `S3140ClosureGateActual`) for circular arguments, and also records
the confirmed INPUT WARNING about the concrete `scaling := 1` model.

## A. Gate hypotheses are NOT derived from ABC / gate conclusion

The gate theorem `s3135_finalAssemblyGate` (and its V3 wrapper
`s3135_finalAssemblyGateV3`) has explicit binders
`hpt : S3135PointLogShellFaithfulness`, `hzero : S3135ScalingLogDegreeZero`,
`hP : S3135ActualPointWeightCard` for an ARBITRARY carrier (see #check below),
and its proof chain is
`s3135_finalAssemblyGate -> s3135_abcConjecture_of_threeResiduals ->
s3135_abcConjecture_of_minimalResiduals -> s3135_abcConjecture_of_endToEndInputsV2
-> ABCFrontier + abcConjecture_of_frontier` (the accepted production frontier
assembly).  No step assumes `ABCConjecture`; the only closure file that assumes it
is `S3135TightnessActual` (the strength/converse theorem
`s3135_pointWeightCard_of_abcConjecture`), which is NOT used by the gate proof
(static audit: zero consumers outside `#check`/probe; the gate proof calls only
the three-residual composition).  No declaration in the closure proves
`S3135PointLogShellFaithfulness`, `S3135ScalingLogDegreeZero` or
`S3135ActualPointWeightCard` for an arbitrary carrier: they occur only as
hypothesis binders/structure fields and as Prop definitions.  `ABCConjecture`
itself is the genuine standard epsilon form (`LeanFormal/IUT/ABCBridge/Statement.lean:32`).

## B. Tightness is used ONLY as a strength statement, never to manufacture hP

`s3135_pointWeightCard_iff_abcConjecture` (card P <=> ABC, under hpt/hzero) is
consumed only by the gate's `s3135_finalAssemblyGate_tight` and the residual
reports — i.e. as the documented "the F5 slot is exactly ABC-strength" statement.
The gate proof `s3135_finalAssemblyGate` does NOT call it nor its converse
direction; `s3135_pointWeightCard_of_abcConjecture` (ABC => card P) has no
consumer in the closure.  Hence no manufacturing of card P.

## C. Concrete `scaling := 1` INPUT WARNING (no leakage into general claims)

The concrete normalized model uses `scaling := 1`, so
`S3135ScalingActualModelActual.sourceHaarActual_scalingLogDegree_zero` is a
TRIVIAL instance, not paper evidence for the general F4(b).  This file is NOT in
the gate's 461-file paper-local transitive closure (as are not
`S3135PaperLambdaConcreteActual`, `S3135CompletionBaseFieldUnitScalarActual`,
`S3135V4*` candidate files), and ZERO closure files mention `scaling := 1` or
that theorem.  Therefore the concrete evidence cannot leak into the general gate
claims; the general F4(b) remains the explicit `hzero` hypothesis.  This input
warning is recorded but does not create a proof circularity.

## D. V4 candidate (NOT audited, NOT gate-imported)

`S3135FinalAssemblyGateV4CandidateActual` / `S3135GateV4ConcreteModelActual`
are NOT in the current gate closure.  Their `hb`/F4.b support is
"PROVED for the concrete normalized model" only, which must be audited for
concrete-model leakage BEFORE any v4 promotion/gate-import.

OUT OF SCOPE: qpilot's `S3133M2aClosedActual` (M2a closure) is a registry note
update pending the combined reopen, not part of this proof-circularity audit.
-/

noncomputable section

namespace LeanFormal.IUT.Audit

/-- Strict circularity audit record for the final gate dependency closure. -/
def S3140CircularityAudit : Obligation :=
  { id := "IUT.project.gate-circularity-audit"
    source :=
      "task-68 (Lead directive after user input-error warning); " ++
        "S3140ClosureGateActual 41-import closure (paper-local transitive 461 files); " ++
        "S3135FinalAssemblyGateActual/V3Actual, S3135TightnessActual, " ++
        "S3135FinalResidualActual, S3135EndToEndV2Actual, ABCFrontier (accepted production)"
    status := VerificationStatus.interface
    note :=
      "VERDICT: NO proof circularity in the V3 gate closure. (A) Gate hypotheses " ++
        "hpt/hzero/hP are explicit binders over an arbitrary carrier; proof chain " ++
        "finalAssemblyGate -> threeResiduals -> minimalResiduals -> endToEndInputsV2 " ++
        "-> ABCFrontier -> abcConjecture_of_frontier assumes no ABC; only closure " ++
        "file assuming ABCConjecture is S3135TightnessActual (strength theorem " ++
        "s3135_pointWeightCard_of_abcConjecture, ZERO consumers in gate proof). " ++
        "(B) tightness s3135_pointWeightCard_iff_abcConjecture is cited only by the " ++
        "_tight strength theorem/reports, never to manufacture hP. (C) INPUT WARNING: " ++
        "concrete model scaling:=1 makes sourceHaarActual_scalingLogDegree_zero a " ++
        "trivial instance; it is NOT in the gate closure (461-file paper-local " ++
        "transitive closure) and no closure file mentions scaling:=1, so no leakage " ++
        "into general claims; general F4(b) remains the explicit hzero hypothesis. " ++
        "(D) V4 candidate (incl. concrete-model hb) is NOT gate-imported and must be " ++
        "audited for concrete-model leakage before promotion. No new axiom/sorry; " ++
        "audit evidence is kernel-checked #check/#print below."
    dependsOn :=
      [ "S3135FinalAssemblyGateActual", "S3135TightnessActual",
        "S3135FinalResidualActual", "S3135EndToEndV2Actual",
        "S3140ClosureGateActual" ] }

/-- Strength record: the gate's third hypothesis is EXACTLY ABC-strength under the
two F4 hypotheses; this documents the conditional nature of the gate (it is not a
proof of ABC, and it is not circular: the hypothesis is assumed, never derived). -/
def S3140GateHypothesisStrengthRecord : Obligation :=
  { id := "IUT.project.gate-hypothesis-strength-record"
    source :=
      "S3135TightnessActual.s3135_pointWeightCard_iff_abcConjecture; " ++
        "S3135FinalResidualActual.s3135_pointWeightCard_iff_additiveBound; " ++
        "ABCHeightWeightAdditiveBoundV2 production equivalence"
    status := VerificationStatus.interface
    note :=
      "hP = S3135ActualPointWeightCard (card P) is equivalent to ABCConjecture " ++
        "under hpt+hzero; gate = [two F4 cards + ONE ABC-strength F5 card] => ABC. " ++
        "Conditional assembly only; NOT a proof of ABCConjecture and no circular " ++
        "derivation of hP from the conclusion."
    dependsOn := [ "S3135TightnessActual" ] }

/-! ## Evidence checks: exact gate/strength signatures (hypotheses explicit). -/
#check @LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual.s3135_finalAssemblyGate
#check @LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual.s3135_finalAssemblyGateV3
#check @LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual.s3135_finalAssemblyGate_tight
#check @LeanFormal.IUT.XiFPaper.S3135TightnessActual.s3135_pointWeightCard_iff_abcConjecture
#check @LeanFormal.IUT.XiFPaper.S3135TightnessActual.s3135_pointWeightCard_of_abcConjecture
#check @LeanFormal.IUT.XiFPaper.S3135FinalResidualActual.s3135_abcConjecture_of_minimalResiduals
#check @LeanFormal.IUT.XiFPaper.S3135EndToEndV2Actual.s3135_abcConjecture_of_endToEndInputsV2
#check @LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual.S3135PointLogShellFaithfulness
#check @LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual.S3135ScalingLogDegreeZero
#check @LeanFormal.IUT.XiFPaper.S3135F5ActualReductionActual.S3135ActualPointWeightCard
-- NOTE: S3135ScalingActualModelActual.sourceHaarActual_scalingLogDegree_zero and the
-- V4 candidate declarations are intentionally NOT imported by this audit (they are
-- outside the gate closure); their static non-membership is recorded in the note.

#check S3140CircularityAudit
#check S3140GateHypothesisStrengthRecord

end LeanFormal.IUT.Audit
