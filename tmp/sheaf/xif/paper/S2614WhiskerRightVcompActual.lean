import tmp.sheaf.xif.paper.S2613C1WhiskerRightCompActual

/-! # S2614: StrongTrans whiskerRight_vcomp -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

namespace LeanFormal.IUT.XiFPaper.S2614WhiskerRightVcompActual

universe u

theorem whiskerRight_vcomp
    {A B C : EtaleStackPseudofunctor S1726K}
    {f g h : Pseudofunctor.StrongTrans A B}
    (η : f ⟶ g) (θ : g ⟶ h) (κ : Pseudofunctor.StrongTrans B C) :
    Pseudofunctor.StrongTrans.whiskerRight (η ≫ θ) κ =
      Pseudofunctor.StrongTrans.whiskerRight η κ
        ≫ Pseudofunctor.StrongTrans.whiskerRight θ κ :=
  CategoryTheory.Bicategory.comp_whiskerRight
    (B := EtaleStackPseudofunctor S1726K)
    (a := A) (b := B) (c := C) η θ κ

#check whiskerRight_vcomp
#print axioms whiskerRight_vcomp

end LeanFormal.IUT.XiFPaper.S2614WhiskerRightVcompActual
end
