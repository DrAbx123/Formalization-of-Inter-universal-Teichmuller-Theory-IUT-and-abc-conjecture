import tmp.sheaf.xif.paper.S3139FirstTriangleRouteCompositionActual
import tmp.sheaf.xif.paper.S3139FirstTriangleM0M1SeamActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: qpilot M1 named residual wired into the route composition

qpilot's exact M1 names (S3133M1ContractSeparatedMissing in
S3133M1ContractObstructionActual; S3133M1Remaining in
S3133M1InjectionReductionActual; proved equivalent) are recorded as Props and
wired into the first-triangle route composition.  The capsule-label link is the
contract-separated extra data field.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139RouteResidualQpilotNamedActual

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
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- qpilot's M1 residual in named form (record-only; exact tree names in the
docstring and in @s3133M1Names@). -/
structure SourceM1QpilotResidual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- S3133M1ContractSeparatedMissing / S3133M1Remaining (iff proved): the
  index equivalence + place agreement. -/
  contractSeparatedMissing : Prop
  /-- the contract-separated capsule-label link Capsule j.val <-> Bad / V. -/
  capsuleLabelLink : Prop

/-- The M1 named residual together with M0 and the stage4 map gives the route
residual record. -/
def SourceM1QpilotResidual.toRouteResidual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (M : SourceM1QpilotResidual I)
    (m0 : Prop) (stage4 : Prop) :
    FirstTriangleRouteResidual I where
  sameCIdentification := m0
  placeSelection := M.contractSeparatedMissing
  stage4UnitMap := stage4

/-- Route composition with the qpilot M1 named residual: only M0 (mainline),
qpilot's M1 named Prop (with proof) and stage4 (with proof) plus the
fourth-triangle arithmetic inputs are assumed. -/
theorem firstTriangleRouteComposition_of_qpilotM1
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
    (M : SourceM1QpilotResidual I)
    (m0 : Prop) (stage4 : Prop)
    (hM0 : m0) (hM1 : M.contractSeparatedMissing) (hStage4 : stage4)
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
    (M.toRouteResidual I m0 stage4) hM0 hM1 hStage4
    n m route hq hullValue hull_negative xif ipl she apt iplEvidence
    sheEvidence aptEvidence

end LeanFormal.IUT.XiFPaper.S3139RouteResidualQpilotNamedActual

end
