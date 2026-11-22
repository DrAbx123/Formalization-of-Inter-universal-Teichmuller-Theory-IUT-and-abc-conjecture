import tmp.sheaf.xif.paper.S3139C2FiniteCopyActionLightActual
import tmp.sheaf.xif.paper.S3139FirstTriangleFieldBActual
import tmp.sheaf.xif.paper.S3139FirstTriangleReadoutActual
import tmp.sheaf.xif.paper.S3139FieldCArchimedeanLogActual
import tmp.sheaf.xif.paper.S3139FirstTriangleFieldACResidualActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

/-!
# S3139: first-triangle integration — conditional theorem

Assembles the constructed first-triangle pieces into one conditional theorem:

* field (A): the source capsule data residual `SourceCapsuleSourceDataMissing`
  (the same datum the (Ind1) bridge depends on);
* field (B): `sourceLGPData`, the actual SourceLGPData built from the actual
  source Theta values (`S3139FirstTriangleFieldBActual`);
* field (C): the archimedean realified copy action (constructed from actual
  archimedean data, supplied here as the archimedean channel) and the
  finite-place channel constructed from the exact C2 data (which reduces to the
  already-owned M0/M1 identifications after stage4's global-units-to-local-units
  maps);
* the S3139 mutation and its post-mutation readouts: the q-pilot log-volume
  -|log q| and the q/Theta comparison seam into the S3138 source V2 boundary.

Remaining residual list (reduced, recorded in `FirstTriangleRemainingResidual`):
C1 source infinite-place choice (III:616-620); C3 tensor-factor identification
(the (Ind1) bridge dependency on field (A)); and the cross-stream M0/M1
ownership.  No sorry/axiom/True/PUnit/toy carrier.

**Component, not paper object.**  Named consumers: lattice/mainline q/Theta
comparison and the registry.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FirstTriangleIntegrationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleMutationActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleResidualActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldACResidualActual
open LeanFormal.IUT.XiFPaper.S3139SourceBPSActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleReadoutActual
open LeanFormal.IUT.XiFPaper.S1265SourceInd2Actual
open LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanLogActual
open LeanFormal.IUT.XiFPaper.S3139FieldCConjugateActual
open LeanFormal.IUT.XiFPaper.S3139C2LocalDegreeDataActual
open LeanFormal.IUT.XiFPaper.S3139C2FiniteCopyActionLightActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The reduced remaining-residual record of the first triangle. -/
structure FirstTriangleRemainingResidual where
  /-- C1: the source infinite-place choice for the archimedean realification. -/
  infinitePlaceChoice : Prop
  /-- field (A)/C3: the source capsule data and the (Ind1) tensor-factor
  identification that depends on it. -/
  sourceCapsuleData : Prop
  /-- cross-stream M0/R1: the same-C identification F ~ F_mod. -/
  sameCIdentification : Prop
  /-- cross-stream M1/R1: the place selection V -> C3.tensorIndex. -/
  placeSelection : Prop

/-- The conditional first-triangle theorem: given the reduced residual data and
the fourth-triangle arithmetic inputs, the copy-action channels exist and the
Corollary 3.12 ordered conclusion follows through the S3138 source V2 boundary. -/
theorem firstTriangleConditional
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I)
    (φ : SourceFmodRealEmbedding (I := I))
    (C1 : SourceInfinitePlaceChoice I.initial.arithmetic)
    (scd : SourceCapsuleSourceDataMissing.{ua, uv, upi, umon, ui, 0, 0, 0, 0}
      Real l V I)
    {F : FPrimeStrip.{umon, uv, upi} V}
    (D : SourceFmodLocalElementMap (l := l) (V := V) F I.initial.arithmetic)
    (j : Fin (capsuleLevels l))
    (vQ : (sourceLGPData I).capsule.VQ)
    (σ : SourceCapsuleFiberAssignment (l := l) V j)
    (arch : SourceInd2CopyActionData Real (sourceLGPData I) j vQ
      (Capsule j.val → (I.initial.arithmetic.Fmod)ˣ))
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
  ⟨⟨sourceCopyActionChannels (F := F) I (sourceLGPData I) D j vQ arch σ⟩,
    (sourceQThetaComparisonInputFromTheta J n m route hq hullValue
      hull_negative xif ipl she apt iplEvidence sheEvidence
      aptEvidence).conclusion⟩

/-- The post-mutation readout side of the conditional theorem: the first
triangle supplies the actual q-pilot log-volume -|log q|; the signed Theta-hull
value and the (xi-f) inclusion remain the fourth-triangle inputs. -/
theorem firstTriangleConditional_qPilot
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (hq : (J.theaterAt 1 0).thetaPacket.q ≠ 1) :
    sourceQPilotSignedLog J < 0 :=
  sourceQPilotSignedLog_neg J hq

/-- The mutation itself is independent of the BPS gluing witness (the paper's
indeterminate input), instantiated at the constructed actual LGP data. -/
theorem firstTriangleConditional_gluing_invariance
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (B : SourceBPS V)
    (glue₁ glue₂ : SourceFTimesMuPrimeStripEquivalence B.timesMuStrip
      (sourceBPSOfTheater J 0 0).timesMuStrip)
    (A : CapsuleTheaterAssignment l V I)
    (φ : SourceFmodRealEmbedding (I := I))
    (j : Fin (capsuleLevels l))
    (vQ : (sourceLGPData I).capsule.VQ)
    (x : (sourceLGPData I).tensorPacket j vQ) :
    (sourceMultiradialMutationOfBPS A (sourceLGPData I) φ j vQ J B glue₁ x).point =
      (sourceMultiradialMutationOfBPS A (sourceLGPData I) φ j vQ J B glue₂ x).point :=
  rfl

end LeanFormal.IUT.XiFPaper.S3139FirstTriangleIntegrationActual

end
