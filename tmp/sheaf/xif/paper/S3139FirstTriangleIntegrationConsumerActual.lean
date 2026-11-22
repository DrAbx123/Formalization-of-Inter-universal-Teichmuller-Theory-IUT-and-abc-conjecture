import tmp.sheaf.xif.paper.S3139FirstTriangleIntegrationActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: first-triangle integration — consumer interface and obligation ids

Public consumer interface of the integrated conditional first-triangle theorem,
plus the exact residual ids for the lattice INDEX and mainline registry.

Supplied data (already constructed elsewhere in this stream unless noted):
field (A) source capsule data residual `SourceCapsuleSourceDataMissing` (the
(Ind1)/C3 dependency), field (B) `sourceLGPData` from the actual source Theta
values, field (C) archimedean realified copy action, the C2 finite-place data
(reduces to cross-stream M0/M1), and the fourth-triangle arithmetic inputs
(signed Theta-hull value and (xi-f) inclusion).  Conclusion: the copy-action
channels exist and the Corollary 3.12 ordered conclusion holds through the
S3138 source V2 boundary.

**Component, not paper object.**  Named consumers: lattice/mainline q/Theta
comparison; mainline registry.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FirstTriangleIntegrationConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleResidualActual
open LeanFormal.IUT.XiFPaper.S1265SourceInd2Actual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleReadoutActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldACResidualActual
open LeanFormal.IUT.XiFPaper.S3139SourceBPSActual
open LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanLogActual
open LeanFormal.IUT.XiFPaper.S3139FieldCConjugateActual
open LeanFormal.IUT.XiFPaper.S3139C2LocalDegreeDataActual
open LeanFormal.IUT.XiFPaper.S3139C2FiniteCopyActionLightActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleIntegrationActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The integrated conditional first-triangle result, exposed to consumers: the
copy-action channels exist and the Corollary 3.12 ordered conclusion follows
from the reduced residual data and the fourth-triangle arithmetic inputs. -/
theorem publicFirstTriangleConditional
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
  firstTriangleConditional I J A φ C1 scd D j vQ σ arch n m route hq
    hullValue hull_negative xif ipl she apt iplEvidence sheEvidence aptEvidence

/-- The reduced remaining-residual ids of the first triangle for the lattice
INDEX / mainline registry (data only). -/
def firstTriangleResidualObligationIds : List (String × String) :=
  [ ("FT.C1.infinite-place-choice",
      "SourceInfinitePlaceChoice (S3139FieldCArchimedeanLogActual; III:616-620)"),
    ("FT.C3.tensor-factor-identification",
      "SourceInd1BridgeDependency (S3139FieldCConjugateActual; depends on FT.A source capsule data)"),
    ("FT.A.source-capsule-data",
      "SourceCapsuleSourceDataMissing (S3139FirstTriangleFieldACResidualActual)"),
    ("FT.C2.conjugate-copy-action",
      "SourceFmodLocalElementMap + SourceCapsuleFiberAssignment (S3139C2LocalDegreeDataActual / S3139C2FiniteCopyActionLightActual)"),
    ("FT.C2.reduces-to-M0-M1",
      "LGPGlobalUnitsLocalMissing (stage4 S3136LGPGlobalUnitsToLocalUnitsActual): sameCIdentification + placeSelection") ]

/-- The constructed first-triangle pieces (data only), for the registry. -/
def firstTriangleConstructedIds : List (String × String) :=
  [ ("FT.A.source-anchored-contract",
      "sourceRealCapsuleContract + SourceLogShellContractMissing_Real_holds (S3139FirstTriangleFieldBActual)"),
    ("FT.B.source-lgp-data",
      "sourceLGPData (S3139FirstTriangleFieldBActual)"),
    ("FT.C.archimedean-realification",
      "sourceFmodArchimedeanLog + sourceFmodArchimedeanScalarCharacter + SourceArchimedeanRealification (S3139FieldCArchimedeanLogActual / S3139FieldCArchimedeanBundleActual)"),
    ("FT.C.copy-action-data",
      "sourceArchimedeanCopyActionData (S3139FieldCCopyActionActual)"),
    ("FT.C2.completion-unit-maps",
      "sourceFmodUnitsToFiniteCompletion / sourceFmodUnitsToInfiniteCompletion (S3139C2FiniteCompletionUnitsActual / S3139C2InfiniteCompletionUnitsActual)"),
    ("FT.C2.finite-copy-action",
      "sourceFinitePlaceCopyActionData + SourceCopyActionChannels (S3139C2FiniteCopyActionLightActual)"),
    ("FT.mutation",
      "sourceMultiradialMutation + gluing invariance (S3139FirstTriangleMutationActual)"),
    ("FT.qpilot-readout",
      "sourceQPilotSignedLog + sourceQPilotSignedLog_neg (S3139FirstTriangleReadoutActual)"),
    ("FT.conditional-theorem",
      "firstTriangleConditional (S3139FirstTriangleIntegrationActual)") ]

end LeanFormal.IUT.XiFPaper.S3139FirstTriangleIntegrationConsumerActual

end
