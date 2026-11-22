import tmp.sheaf.xif.paper.MultiradialProcessionActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
namespace LeanFormal.IUT.XiFPaper.S3128ProcessionTransActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {A : CapsuleTheaterAssignment l V I}
variable {j : Fin (capsuleLevels l)}

theorem PrcTransition_trans_refl_left (i i' : Capsule j.val) :
    FPrimeStripEquiv.trans (FPrimeStripEquiv.refl (PrcMember A j i))
      (PrcTransition A j i i') = PrcTransition A j i i' :=
  FPrimeStripEquiv.trans_refl_left

theorem PrcTransition_trans_refl_right (i i' : Capsule j.val) :
    FPrimeStripEquiv.trans (PrcTransition A j i i')
      (FPrimeStripEquiv.refl (PrcMember A j i')) = PrcTransition A j i i' :=
  FPrimeStripEquiv.trans_refl_right

theorem PrcTransition_trans_assoc (i i' i'' i''' : Capsule j.val) :
    FPrimeStripEquiv.trans
      (FPrimeStripEquiv.trans (PrcTransition A j i i')
        (PrcTransition A j i' i''))
      (PrcTransition A j i'' i''') =
    FPrimeStripEquiv.trans (PrcTransition A j i i')
      (FPrimeStripEquiv.trans (PrcTransition A j i' i'')
        (PrcTransition A j i'' i''')) :=
  FPrimeStripEquiv.trans_assoc

#check PrcTransition_trans_refl_left
#check PrcTransition_trans_refl_right
#check PrcTransition_trans_assoc
end LeanFormal.IUT.XiFPaper.S3128ProcessionTransActual