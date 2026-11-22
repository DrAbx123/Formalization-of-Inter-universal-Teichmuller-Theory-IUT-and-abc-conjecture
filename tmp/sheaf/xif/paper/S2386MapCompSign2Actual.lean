import tmp.sheaf.xif.paper.S2332PsubCorrectActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2332PsubCorrectActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2259QMapPrecompActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2386MapCompSign2Actual

variable {A B C : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ}
variable (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (hh : f ≫ g = h)
variable (M : S2152Q.obj A)

-- Exact #check output:
-- (Pseudofunctor.mapComp' S2152Q f g h hh).hom.toNatTrans.app M :
--   (S2152Q.map h).toFunctor.obj M ⟶
--     (S2152Q.map f ≫ S2152Q.map g).toFunctor.obj M
--
-- Here M is an object of the category S2152Q.obj A, and the app component is a
-- natural-transformation component, i.e. a 1-morphism in Cat (a functor), not a
-- SignGroup-labelled action-category morphism.  Therefore val is not the sign
-- label; the earlier val = 1 statement is ill-typed.
#check (S2152Q.mapComp' f g h hh).hom.toNatTrans.app M
#check S1971PrecompFunctor_map_val
#check S2259QMapPrecomp

end LeanFormal.IUT.XiFPaper.S2386MapCompSign2Actual

end
