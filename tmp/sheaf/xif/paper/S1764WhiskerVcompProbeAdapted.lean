import tmp.sheaf.xif.paper.S1763HomVcompActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
namespace LeanFormal.IUT.XiFPaper.S1764WhiskerVcompProbeAdapted

variable {F : Type} [Field F]
variable {W X Y : EtaleStackPseudofunctor F}

example {f g : Pseudofunctor.StrongTrans W X} (η : f ≅ g)
    (h : Pseudofunctor.StrongTrans X Y) :
    Iso (Pseudofunctor.StrongTrans.vcomp f h)
      (Pseudofunctor.StrongTrans.vcomp g h) := by
  change Iso (f ≫ h) (g ≫ h)
  exact Bicategory.whiskerRightIso η h

end LeanFormal.IUT.XiFPaper.S1764WhiskerVcompProbeAdapted
