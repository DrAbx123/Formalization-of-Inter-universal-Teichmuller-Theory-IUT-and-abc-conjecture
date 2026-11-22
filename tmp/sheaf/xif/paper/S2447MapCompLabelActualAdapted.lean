import tmp.sheaf.xif.paper.S2427PsubNatIsoConditionalActual
import tmp.sheaf.xif.paper.S1971ActionStackificationActual

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

namespace LeanFormal.IUT.XiFPaper.S2447MapCompLabelActualAdapted

variable {A B C : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ}
variable (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (hh : f ≫ g = h)
variable (M : S2152Q.obj A)

theorem S2447_mapComp_label :
    ((S2152PFunctor.toPseudofunctor'.mapComp' f g h hh).hom.toNatTrans.app M).1 = 1 := by
  subst hh
  rfl

#print axioms S2447_mapComp_label

end LeanFormal.IUT.XiFPaper.S2447MapCompLabelActualAdapted

end
