import tmp.sheaf.xif.paper.S2578CastBothActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2630CastHelpersActual
open LeanFormal.IUT.XiFPaper.S2578CastBothActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2579CastIsoTargetActualAdapted

universe u
variable {F : Type u} [Field F]
variable {P Q R R' : Iut.EtaleStackPseudofunctor F}

noncomputable def castIsoTarget (k : R = R')
    {L1 L2 : Pseudofunctor.StrongTrans P R}
    (e : Iso L1 L2) :
    Iso (castTarget (F := F) k L1) (castTarget (F := F) k L2) := by
  cases k
  exact e

theorem castBoth_cancel (h : P = Q)
    (L : Pseudofunctor.StrongTrans P P) :
    castTarget (F := F) h.symm
      (castStrongTrans (R := P) h.symm (castStrongTrans (R := P) h L)) = L := by
  cases h
  rfl

theorem castBoth_id' (h : P = Q) :
    castTarget (F := F) h.symm
      (castStrongTrans (R := Q) h.symm (Pseudofunctor.StrongTrans.id Q)) =
      Pseudofunctor.StrongTrans.id P := by
  cases h
  rfl

#print axioms castIsoTarget
#print axioms castBoth_cancel
#print axioms castBoth_id'

end LeanFormal.IUT.XiFPaper.S2579CastIsoTargetActualAdapted
end
