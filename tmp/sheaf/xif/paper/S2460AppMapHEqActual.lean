import tmp.sheaf.xif.paper.S2459AppHEqActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2460AppMapHEqActual

variable {A B C : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ}
variable (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (hh : f ≫ g = h)
variable (M : S2152Q.obj A)
variable {X Y : (S2152PFunctor.toPseudofunctor'.map h).toFunctor.obj M}
variable (x : X ⟶ Y)

theorem S2460_app_map_heq :
    HEq (((S2152PFunctor.toPseudofunctor'.mapComp' f g h hh).hom.toNatTrans.app M).map x) x := by
  cases hh
  rfl

#print axioms S2460_app_map_heq

end LeanFormal.IUT.XiFPaper.S2460AppMapHEqActual

end
