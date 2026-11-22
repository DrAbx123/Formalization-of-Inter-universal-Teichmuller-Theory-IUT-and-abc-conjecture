import tmp.sheaf.xif.paper.S3139FirstTriangleFinalCompositionLightActual
import tmp.sheaf.xif.paper.S3139C3ConventionClosureActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: first-triangle ROUTE COMPOSITION — final conditional theorem with the C3 closure consumed

After the certified C3 closure (@S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds),
the first-triangle HARD composition no longer takes the convention identification
as a hypothesis: it is supplied internally.  The remaining hypotheses are the
route residual data (cross-stream M0 same-C, M1 place selection + capsule-label
link, stage4 unit map as recorded exact data) plus the fourth-triangle
arithmetic inputs.  Conclusion: the complete copy-action channels exist and the
Corollary 3.12 ordered conclusion holds through the S3138 source V2 boundary.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FirstTriangleRouteCompositionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S1265SourceInd2Actual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleResidualActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleReadoutActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldACResidualActual
open LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanLogActual
open LeanFormal.IUT.XiFPaper.S3139C1InfinitePlaceActual
open LeanFormal.IUT.XiFPaper.S3139C2LocalDegreeDataActual
open LeanFormal.IUT.XiFPaper.S3139C2FiniteCopyActionLightActual
open LeanFormal.IUT.XiFPaper.S3139C3Ind1BridgeActual
open LeanFormal.IUT.XiFPaper.S3139C3ConventionClosureActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFinalCompositionLightActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The route residual record of the first triangle after the C3 closure: the
exact remaining data are the cross-stream M0/M1 identifications (mainline R1 /
qpilot M1, including the contract-separated capsule-label link) and the stage4
canonical unit map. -/
structure FirstTriangleRouteResidual (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- M0/R1 same-C identification F ~ F_mod (mainline). -/
  sameCIdentification : Prop
  /-- M1/R1 place selection (qpilot S3133M1ContractSeparatedMissing /
  S3133M1Remaining) including the contract-separated capsule-label link. -/
  placeSelection : Prop
  /-- stage4 canonical global-units-to-local-units map
  (S3136LGPGlobalUnitsToLocalUnitsActual.lgpGlobalUnitsToLocalUnits). -/
  stage4UnitMap : Prop

/-- The first-triangle ROUTE COMPOSITION theorem: the C3 convention
identification is discharged internally by the certified closure, so the only
hypotheses are the route residual data and the fourth-triangle arithmetic
inputs; conclusion: copy-action channels exist AND Cor312Conclusion. -/
theorem firstTriangleRouteComposition
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I)
    (φ : SourceFmodRealEmbedding (I := I))
    (scd : SourceCapsuleSourceDataMissing.{ua, uv, upi, umon, ui, 0, 0, 0, 0}
      Real l V I)
    {F : FPrimeStrip.{umon, uv, upi} V}
    (D : SourceFmodLocalElementMap (l := l) (V := V) F I.initial.arithmetic)
    (j : Fin (capsuleLevels l)) (vQ : (sourceLGPData I).capsule.VQ)
    (σ : SourceCapsuleFiberAssignment (l := l) V j)
    (R : FirstTriangleRouteResidual I)
    (hM0 : R.sameCIdentification) (hM1 : R.placeSelection)
    (hStage4 : R.stage4UnitMap)
    (n m : Int) (route : List (RouteStep SourceStepXILabel))
    (hq : (J.theaterAt 1 0).thetaPacket.q ≠ 1)
    (hullValue : ℝ) (hull_negative : hullValue < 0)
    (xif : sourceQPilotSignedLog J ≤ hullValue)
    (ipl she apt : Prop) (iplEvidence : ipl) (sheEvidence : she)
    (aptEvidence : apt) :
    Nonempty (SourceCopyActionChannels (F := F) I (sourceLGPData I) j vQ) ∧
      Cor312Conclusion
        ((sourceQThetaComparisonInputFromTheta J n m route hq hullValue
          hull_negative xif ipl she apt iplEvidence sheEvidence
          aptEvidence).boundary.assembly.arithmetic.toContract) :=
  firstTriangleFinalComposition I J A φ scd D j vQ σ
    (sourceInd1ConventionIdentification_holds I A)
    R.sameCIdentification R.placeSelection R.placeSelection
    n m route hq hullValue hull_negative xif ipl she apt iplEvidence
    sheEvidence aptEvidence

end LeanFormal.IUT.XiFPaper.S3139FirstTriangleRouteCompositionActual

end
