import tmp.sheaf.xif.paper.S3139RouteResidualQpilotNamedActual
import tmp.sheaf.xif.paper.S3139RouteResidualMainlineM0NamedActual
import tmp.sheaf.xif.paper.S3139RouteCapsuleLabelResidualActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: first-triangle route FINAL HARDENED composition (all named residuals explicit)

Consumes mainline's M0 same-C named residual, qpilot's M1 named residual
(S3133M1ContractSeparatedMissing / S3133M1Remaining), the contract-separated
capsule-label link residual, and the stage4 unit map -- the exact residual list
after the certified C3 closure.  No convention-identification hypothesis remains
(discharged internally), and no volume/measure invariance is silently assumed.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139RouteFinalCompositionHardenedActual

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
open LeanFormal.IUT.XiFPaper.S3139RouteResidualQpilotNamedActual
open LeanFormal.IUT.XiFPaper.S3139RouteResidualMainlineM0NamedActual
open LeanFormal.IUT.XiFPaper.S3139RouteCapsuleLabelResidualActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The final exact residual list of the first-triangle route after the C3
closure: mainline M0, qpilot M1, capsule-label link, stage4 unit map. -/
structure SourceRouteHardenedResidual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (j : Fin (capsuleLevels l)) where
  /-- mainline M0 same-C identification -/
  m0 : SourceM0MainlineResidual I
  /-- qpilot M1 residual (index equivalence + place agreement) -/
  m1 : SourceM1QpilotResidual I
  /-- contract-separated capsule-label link -/
  capsuleLabelLink : SourceCapsuleLabelLinkResidual I j
  /-- stage4 canonical unit map (as a Prop slot) -/
  stage4UnitMap : Prop

/-- The first-triangle route composition with ALL named residuals explicit:
conclusion = copy-action channels exist + Corollary 3.12 ordered conclusion. -/
theorem firstTriangleRouteFinalComposition
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
    (R : SourceRouteHardenedResidual I j)
    (hM0 : R.m0.sameCIdentification)
    (hM1 : R.m1.contractSeparatedMissing)
    (hLabel : R.capsuleLabelLink.capsuleLabelLink)
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
  firstTriangleRouteComposition_with_capsuleLabel I J A φ scd D j vQ σ
    R.m0.sameCIdentification R.m1.contractSeparatedMissing R.stage4UnitMap
    R.capsuleLabelLink hM0 hM1 hLabel hStage4
    n m route hq hullValue hull_negative xif ipl she apt iplEvidence
    sheEvidence aptEvidence

end LeanFormal.IUT.XiFPaper.S3139RouteFinalCompositionHardenedActual

end
