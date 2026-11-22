import tmp.sheaf.xif.paper.S3139FirstTriangleRouteCompositionActual
import tmp.sheaf.xif.paper.S3139RouteComparisonInvarianceActual
import tmp.sheaf.xif.paper.S3139ComparisonMeasureInvarianceResidualActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: first-triangle route FINAL RESIDUAL record (all named residuals bundled)

Bundles the complete first-triangle route residual after the C3 closure:
* the route composition residual data (M0 same-C, M1 place selection +
  capsule-label link, stage4 unit map);
* the V2 comparison/measure-invariance residuals
  (FT.route.comparison-invariance / FT.route.measure-invariance).
The route composition theorem is provided from the bundled record, so consumers
see one exact residual object.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139RouteFinalResidualActual

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
open LeanFormal.IUT.XiFPaper.S3139C1InfinitePlaceActual
open LeanFormal.IUT.XiFPaper.S3139C2LocalDegreeDataActual
open LeanFormal.IUT.XiFPaper.S3139C2FiniteCopyActionLightActual
open LeanFormal.IUT.XiFPaper.S3139C3Ind1BridgeActual
open LeanFormal.IUT.XiFPaper.S3139C3ConventionClosureActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFinalCompositionLightActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleRouteCompositionActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The complete first-triangle route residual record after the C3 closure. -/
structure SourceRouteFinalResidual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- M0/M1/stage4 route residual data -/
  route : FirstTriangleRouteResidual I
  /-- FT.route.comparison-invariance: log-volume invariance under the C3
  comparison (mainline S3131RouteComparisonInvarianceHypothesis). -/
  comparisonInvariance : Prop
  /-- FT.route.measure-invariance: Haar/log-volume invariance under the C3
  comparison (abc S3135ComparisonMeasureInvariance). -/
  measureInvariance : Prop

/-- The route composition from the bundled final residual. -/
theorem firstTriangleRouteComposition_of_finalResidual
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
    (R : SourceRouteFinalResidual I)
    (hM0 : R.route.sameCIdentification)
    (hM1 : R.route.placeSelection)
    (hStage4 : R.route.stage4UnitMap)
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
  firstTriangleRouteComposition I J A φ scd D j vQ σ R.route hM0 hM1 hStage4
    n m route hq hullValue hull_negative xif ipl she apt iplEvidence
    sheEvidence aptEvidence

end LeanFormal.IUT.XiFPaper.S3139RouteFinalResidualActual

end
