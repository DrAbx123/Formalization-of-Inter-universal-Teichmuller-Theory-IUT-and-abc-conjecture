import tmp.sheaf.xif.paper.S3139TensorPacketScalarLogVolumeActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: procession tensor-packet log-volume (vendor-adapted)

Adapted from vendor promachina Iut/Stage1/IUTStage1SourceCore.lean:1299
structure IUTStage1ProcessionTensorPacketLogVolume (and its fiber version at
:1392): a linear log-volume readout of the tensor packet, here as a structure
with the additivity and homogeneity laws, constructible from ANY linear
functional; and the LGP scalar-action law for its acted value (the vendor
relation IUTStage1Gaussian.lean:3629 in linear-readout form).

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139VendorProcessionLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- A procession tensor-packet log-volume readout: a real-valued function on the
tensor packet with additivity and homogeneity (linear-functional form). -/
structure SourceProcessionTensorPacketLogVolume
    (D : SourceLGPData Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : D.capsule.VQ) where
  /-- the log-volume value -/
  logVolume : D.tensorPacket j vQ → ℝ
  /-- additivity over the tensor packet -/
  logVolume_add : ∀ x y, logVolume (x + y) = logVolume x + logVolume y
  /-- homogeneity in the real scalars -/
  logVolume_smul : ∀ (a : ℝ) (x), logVolume (a • x) = a * logVolume x

/-- Every linear functional on the tensor packet yields a procession
tensor-packet log-volume readout. -/
def sourceProcessionTensorPacketLogVolumeOfLinear
    (D : SourceLGPData Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : D.capsule.VQ)
    (ℓ : D.tensorPacket j vQ →ₗ[Real] Real) :
    SourceProcessionTensorPacketLogVolume D j vQ where
  logVolume := ℓ
  logVolume_add := fun x y => map_add ℓ x y
  logVolume_smul := fun a x => map_smul ℓ a x

/-- The acted log-volume under the LGP splitting-monoid action is the scalar
character times the original log-volume (vendor relation
actedTensorPacketLogVolume_eq_original_plus_generators, linear form). -/
theorem SourceProcessionTensorPacketLogVolume.logVolume_action
    (D : SourceLGPData Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : D.capsule.VQ)
    (V' : SourceProcessionTensorPacketLogVolume D j vQ)
    (g : D.lgp.Carrier) (x : D.tensorPacket j vQ) :
    V'.logVolume ((D.actionOnTensorPacket j vQ) g x) =
      ((D.action j).scalar g : Real) * V'.logVolume x := by
  rw [SourceLGPData.actionOnTensorPacket,
    LGPMonoidAction.actionOnTensorPacket_apply]
  exact V'.logVolume_smul ((D.action j).scalar g) x

end LeanFormal.IUT.XiFPaper.S3139VendorProcessionLogVolumeActual

end
