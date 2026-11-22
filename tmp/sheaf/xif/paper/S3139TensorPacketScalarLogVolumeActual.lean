import tmp.sheaf.xif.paper.S3139FirstTriangleFieldBActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: tensor-packet log-volume readout under the LGP scalar action (vendor-adapted)

Adapted from the vendor promachina Stage1 relation
LGPSplittingMonoidTensorPacketAction.actedTensorPacketLogVolume_eq_original_plus_generators
(Iut/Stage1/IUTStage1Gaussian.lean:3629): the LGP splitting-monoid action on the
tensor packet acts on ANY linear log-volume readout by multiplication with the
action's scalar character.  This is the linear-readout form needed by the
paper-route source-side log-volume comparison.

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139TensorPacketScalarLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- A linear log-volume readout of the tensor packet is multiplied by the LGP
scalar character of the acting splitting-monoid element. -/
theorem sourceLGP_linearReadout_action
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (D : SourceLGPData Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : D.capsule.VQ)
    (g : D.lgp.Carrier)
    (ℓ : D.tensorPacket j vQ →ₗ[Real] Real)
    (x : D.tensorPacket j vQ) :
    ℓ ((D.actionOnTensorPacket j vQ) g x) =
      ((D.action j).scalar g : Real) * ℓ x := by
  rw [SourceLGPData.actionOnTensorPacket,
    LGPMonoidAction.actionOnTensorPacket_apply]
  exact (ℓ.map_smul ((D.action j).scalar g) x)

end LeanFormal.IUT.XiFPaper.S3139TensorPacketScalarLogVolumeActual

end
