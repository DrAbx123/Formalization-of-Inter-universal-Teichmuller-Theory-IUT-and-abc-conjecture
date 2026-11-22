import tmp.sheaf.xif.paper.MultiradialProcessionActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
namespace LeanFormal.IUT.XiFPaper.S3128MultiradialInd1Actual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {A : CapsuleTheaterAssignment l V I}
variable {j : Fin (capsuleLevels l)}

theorem PrcAutomorphism.ofPerm_perm (sigma : Capsule j.val ≃ Capsule j.val) :
    (PrcAutomorphism.ofPerm A j sigma).perm = sigma := rfl

theorem PrcAutomorphism.ofPerm_component (sigma : Capsule j.val ≃ Capsule j.val)
    (i : Capsule j.val) :
    (PrcAutomorphism.ofPerm A j sigma).component i =
      PrcTransition A j i (sigma i) := rfl

theorem PrcAutomorphism.id_component (i : Capsule j.val) :
    (PrcAutomorphism.id A j).component i =
      FPrimeStripEquiv.refl (PrcMember A j i) := by
  unfold PrcAutomorphism.id PrcAutomorphism.ofPerm
  exact PrcTransition_refl A j i

theorem PrcAutomorphism.comp_perm (sigma tau : PrcAutomorphism A j) :
    (PrcAutomorphism.comp A j sigma tau).perm =
      sigma.perm.trans tau.perm := rfl

theorem PrcAutomorphism.comp_component (sigma tau : PrcAutomorphism A j)
    (i : Capsule j.val) :
    (PrcAutomorphism.comp A j sigma tau).component i =
      FPrimeStripEquiv.trans (sigma.component i)
        (tau.component (sigma.perm i)) := rfl

theorem PrcAutomorphism.ofPerm_refl_component (i : Capsule j.val) :
    (PrcAutomorphism.ofPerm A j (Equiv.refl (Capsule j.val))).component i =
      FPrimeStripEquiv.refl (PrcMember A j i) := by
  simpa [PrcAutomorphism.ofPerm] using PrcTransition_refl A j i

#check PrcAutomorphism.ofPerm_perm
#check PrcAutomorphism.id_component
#check PrcAutomorphism.comp_component
#check PrcAutomorphism.ofPerm_refl_component
end LeanFormal.IUT.XiFPaper.S3128MultiradialInd1Actual