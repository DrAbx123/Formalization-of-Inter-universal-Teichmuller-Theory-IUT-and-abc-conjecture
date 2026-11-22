import tmp.sheaf.xif.paper.S3139FirstTriangleRouteCompositionActual
import tmp.sheaf.xif.paper.S3139FirstTriangleM0M1SeamActual
import tmp.sheaf.xif.paper.S3139FirstTriangleStage4SeamActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: named route residuals -> final composition

Wires the cross-stream named residuals (M0 same-C, M1 place selection including
the capsule-label link, stage4 unit map) into the first-triangle route
composition theorem.  Consumers supply the named data as Props with proofs; the
C3 convention identification is discharged internally by the certified closure.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139RouteResidualNamedActual

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
open LeanFormal.IUT.XiFPaper.FirstTriangleM0M1SeamActual
open LeanFormal.IUT.XiFPaper.FirstTriangleStage4SeamActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The named route residual package (cross-stream names as Props). -/
structure SourceRouteResidualNamed
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- M0 same-C identification seam -/
  m0 : SourceM0M1Seam
  /-- stage4 unit-map seam -/
  stage4 : SourceStage4UnitMapSeam

/-- Build the route residual record from the named seams. -/
def SourceRouteResidualNamed.toRouteResidual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (R : SourceRouteResidualNamed I) :
    FirstTriangleRouteResidual I where
  sameCIdentification := R.m0.sameCIdentification
  placeSelection := R.m0.placeSelection
  stage4UnitMap := R.stage4.unitMap

/-- The route composition with named cross-stream residuals: only the named
residual data (M0, M1 + label link, stage4) and the fourth-triangle arithmetic
inputs are assumed; the C3 convention identification is discharged internally. -/
theorem firstTriangleRouteComposition_of_named
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
    (R : SourceRouteResidualNamed I)
    (hM0 : R.m0.sameCIdentification) (hM1 : R.m0.placeSelection)
    (hStage4 : R.stage4.unitMap)
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
  firstTriangleRouteComposition I J A φ scd D j vQ σ
    R.toRouteResidual hM0 hM1 hStage4
    n m route hq hullValue hull_negative xif ipl she apt iplEvidence
    sheEvidence aptEvidence

end LeanFormal.IUT.XiFPaper.S3139RouteResidualNamedActual

end
