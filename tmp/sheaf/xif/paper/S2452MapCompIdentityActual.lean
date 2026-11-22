import tmp.sheaf.xif.paper.S2445SignProjectionActual
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
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2452MapCompIdentityActual

variable {A B C : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ}
variable (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (hh : f ≫ g = h)
variable (M : S2152Q.obj A)

/-- The underlying base function of the mapComp' coherence app is the identity. -/
theorem S2452_mapComp_fun_id :
    ((S2152PFunctor.toPseudofunctor'.mapComp' f g h hh).hom.toNatTrans.app M).1 = 𝟙 _ := by
  rfl

#print axioms S2452_mapComp_fun_id

end LeanFormal.IUT.XiFPaper.S2452MapCompIdentityActual

end
