import tmp.sheaf.xif.paper.S3139FirstTriangleIntegrationActual
import tmp.sheaf.xif.paper.S3139C1InfinitePlaceActual
import tmp.sheaf.xif.paper.S3139C3Ind1BridgeActual
import tmp.sheaf.xif.paper.S3139C2FiniteCopyActionLightActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 600000

/-!
# S3139: first-triangle FINAL COMPOSITION (light) — conditional theorem consuming resolved C1

After the resolutions in this stream:

* C1 (source infinite-place choice) is RESOLVED: the archimedean Real scalar
  character is constructed with NO supplied place (`sourceArchimedeanScalarActual,
  S3139C1InfinitePlaceActual);
* C3 dependency is DISCHARGED (`sourceInd1BridgeDependency_Real_holds); the
  exact remaining datum is `SourceInd1ConventionIdentification`;
* C2 is reduced to cross-stream M0/M1 (same-C identification + place selection,
  owned-by-qpilot names S3133M1ContractSeparatedMissing / S3133M1Remaining,
  plus the capsule-label link which is contract-separated) with stage4's
  canonical global-units-to-local-units map.

This file assembles the final composition theorem: taking the remaining exact
data as explicit hypotheses, the complete copy-action channels exist
(archimedean channel from the RESOLVED C1, finite-place channel from the C2
data) and the Corollary 3.12 ordered conclusion follows from the
fourth-triangle arithmetic inputs.

**Component, not paper object.**  Registry FROZEN (final status/ledger only).
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FirstTriangleFinalCompositionLightActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
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
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The archimedean realified copy action data built from the RESOLVED C1 (the
actual archimedean Real scalar character, no supplied infinite place). -/
noncomputable def sourceArchimedeanCopyActionDataOfActual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (Dlgp : SourceLGPData Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : Dlgp.capsule.VQ) :
    SourceInd2CopyActionData Real Dlgp j vQ
      (Capsule j.val → (I.initial.arithmetic.Fmod)ˣ) where
  action := fun f => ind2TensorEquiv (C := Dlgp.capsule) (j := j) (vQ := vQ)
    (fun i => sourceArchimedeanScalarActual I.initial.arithmetic (f i))
  action_one := by
    have h : (fun i => sourceArchimedeanScalarActual I.initial.arithmetic
        ((1 : Capsule j.val → (I.initial.arithmetic.Fmod)ˣ) i)) =
        (1 : Capsule j.val → ℝˣ) := by
      funext i
      exact map_one (sourceArchimedeanScalarActual I.initial.arithmetic)
    rw [h]
    exact lightInd2_one
  action_mul := by
    intro c d
    have hfun : (fun i => sourceArchimedeanScalarActual I.initial.arithmetic
        ((c * d) i)) =
        (fun i => sourceArchimedeanScalarActual I.initial.arithmetic (c i)) *
          (fun i => sourceArchimedeanScalarActual I.initial.arithmetic (d i)) := by
      funext i
      exact map_mul (sourceArchimedeanScalarActual I.initial.arithmetic) (c i) (d i)
    rw [hfun]
    exact lightInd2_mul
      (fun i => sourceArchimedeanScalarActual I.initial.arithmetic (c i))
      (fun i => sourceArchimedeanScalarActual I.initial.arithmetic (d i))
  action_scalar := by
    intro c g x
    show ind2TensorEquiv (C := Dlgp.capsule) (j := j) (vQ := vQ)
        (fun i => sourceArchimedeanScalarActual I.initial.arithmetic (c i))
        (((Dlgp.action j).scalar g) • x) =
      ((Dlgp.action j).scalar g) •
        ind2TensorEquiv (C := Dlgp.capsule) (j := j) (vQ := vQ)
          (fun i => sourceArchimedeanScalarActual I.initial.arithmetic (c i)) x
    exact (ind2TensorEquiv (C := Dlgp.capsule) (j := j) (vQ := vQ)
      (fun i => sourceArchimedeanScalarActual I.initial.arithmetic (c i))).map_smul
        ((Dlgp.action j).scalar g) x

/-- The final composition's residual record: the exact remaining data of the
first triangle after the C1/C3 resolutions. -/
structure FirstTriangleFinalResidual where
  /-- field (A)/C3: the (Ind1) convention identification (exact datum). -/
  conventionIdentification : Prop
  /-- cross-stream M0/R1: the same-C identification F ~ F_mod (mainline R1). -/
  sameCIdentification : Prop
  /-- cross-stream M1/R1: owned-by-qpilot exact missing
  S3133M1ContractSeparatedMissing / S3133M1Remaining (index equivalence +
  place agreement; contract-separated). -/
  placeSelection : Prop
  /-- C2 contract-separated capsule-label link: Capsule j.val <-> Bad / V
  (not in the tree; extra data field of the fiber assignment). -/
  capsuleLabelLink : Prop

/-- The first-triangle FINAL COMPOSITION theorem: given the remaining exact
data as hypotheses and the fourth-triangle arithmetic inputs, the complete
copy-action channels exist (archimedean channel constructed from the RESOLVED
C1) and the Corollary 3.12 ordered conclusion follows. -/
theorem firstTriangleFinalComposition
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
    (hconv : SourceInd1ConventionIdentification I A)
    (hM0 : Prop) (hM1 : Prop) (hLabel : Prop)
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
  ⟨⟨sourceCopyActionChannels (F := F) I (sourceLGPData I) D j vQ
      (sourceArchimedeanCopyActionDataOfActual I (sourceLGPData I) j vQ) σ⟩,
    (sourceQThetaComparisonInputFromTheta J n m route hq hullValue
      hull_negative xif ipl she apt iplEvidence sheEvidence
      aptEvidence).conclusion⟩

end LeanFormal.IUT.XiFPaper.S3139FirstTriangleFinalCompositionLightActual

end
