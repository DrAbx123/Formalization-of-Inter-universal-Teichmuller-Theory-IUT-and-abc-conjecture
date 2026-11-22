import tmp.sheaf.xif.paper.S2453MapCompIdProofActual
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

namespace LeanFormal.IUT.XiFPaper.S2456AppEqToIsoActual

variable {A B C : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ}
variable (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (hh : f ≫ g = h)
variable (M : S2152Q.obj A)

/-- The comparison equality of functors from h to f ≫ g. -/
def S2456e : S2152PFunctor.map h.as = S2152PFunctor.map f.as ≫ S2152PFunctor.map g.as := by
  cases hh
  exact S2152PFunctor.map_comp f.as g.as

/-- The mapComp' app equals the eqToIso induced by S2456e. -/
theorem S2456_app_eq_eqToIso :
    ((S2152PFunctor.toPseudofunctor'.mapComp' f g h hh).hom.toNatTrans.app M) =
      (eqToIso (S2456e f g h hh)).hom.toNatTrans.app M := by
  cases hh
  rfl

#print axioms S2456_app_eq_eqToIso

end LeanFormal.IUT.XiFPaper.S2456AppEqToIsoActual

end
