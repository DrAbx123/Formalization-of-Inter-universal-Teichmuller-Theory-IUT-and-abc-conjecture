import tmp.sheaf.xif.paper.S2619RightCancellationActual

/-! # S2624: RightCancellation for the identity 1-cell -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2619RightCancellationActual

namespace LeanFormal.IUT.XiFPaper.S2624RightCancellationIdActual

universe u

noncomputable def idRightCancellation (Y : EtaleStackOverField S1726K) :
    RightCancellation (𝟙 Y.fiber) where
  cancelRight A B e := by
    have e' : Iso (A ≫ 𝟙 Y.fiber) (B ≫ 𝟙 Y.fiber) := e
    exact (Pseudofunctor.StrongTrans.rightUnitor A).symm.trans
      (e'.trans (Pseudofunctor.StrongTrans.rightUnitor B))

#check idRightCancellation
#print axioms idRightCancellation

end LeanFormal.IUT.XiFPaper.S2624RightCancellationIdActual
end
