import tmp.sheaf.xif.paper.S2578CastBothActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2583CastIso2Actual

universe u
variable {F : Type u} [Field F]
variable {P Q R S : Iut.EtaleStackPseudofunctor F}

noncomputable def castStrongTrans2 (h : P = Q) (k : R = S)
    (L : Pseudofunctor.StrongTrans P R) : Pseudofunctor.StrongTrans Q S := by
  cases h
  cases k
  exact L

noncomputable def castIso2 (h : P = Q) (k : R = S)
    {L1 L2 : Pseudofunctor.StrongTrans P R} (e : Iso L1 L2) :
    Iso (castStrongTrans2 h k L1) (castStrongTrans2 h k L2) := by
  cases h
  cases k
  exact e

noncomputable def castStrongTrans2_id (h : P = Q) :
    castStrongTrans2 h h (Pseudofunctor.StrongTrans.id P) =
      Pseudofunctor.StrongTrans.id Q := by
  cases h
  rfl

#print axioms castIso2
#print axioms castStrongTrans2_id

end LeanFormal.IUT.XiFPaper.S2583CastIso2Actual
end
