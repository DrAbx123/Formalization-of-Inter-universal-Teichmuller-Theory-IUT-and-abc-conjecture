import tmp.sheaf.xif.paper.S2576CoverIsoFinalActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2630CastHelpersActual
open LeanFormal.IUT.XiFPaper.S2576CoverIsoFinalActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2578CastBothActual

universe u
variable {F : Type u} [Field F]
variable {P Q R R' : Iut.EtaleStackPseudofunctor F}

noncomputable def castTarget (k : R = R')
    (L : Pseudofunctor.StrongTrans P R) :
    Pseudofunctor.StrongTrans P R' := by
  cases k
  exact L

noncomputable def castBoth (h : P = Q)
    (L : Pseudofunctor.StrongTrans P P) :
    Pseudofunctor.StrongTrans Q Q := by
  cases h
  exact L

theorem castBoth_id (h : P = Q) :
    castBoth h (Pseudofunctor.StrongTrans.id P) =
      Pseudofunctor.StrongTrans.id Q := by
  cases h
  rfl

#print axioms castBoth_id

end LeanFormal.IUT.XiFPaper.S2578CastBothActual
end
