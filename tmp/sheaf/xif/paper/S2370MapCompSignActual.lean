import tmp.sheaf.xif.paper.S2366QHomSignProjectionActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2366QHomSignProjectionActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2259QMapPrecompActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2370MapCompSignActual

variable {A B C : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ}
variable (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (hh : f ≫ g = h)

-- The intended lemma
--   ((S2152Q.mapComp' f g h hh).hom.toNatTrans.app M).val = 1
-- does not typecheck as stated: the app component is a morphism in the base
-- Type of the action category, not a SignGroup-labelled action-category
-- morphism.  The correct formulation needs the action-category morphism
-- projection (or the corresponding natural transformation component), and was
-- not found in the available time.
#check S1971PrecompFunctor_map_val
#check S2259QMapPrecomp

end LeanFormal.IUT.XiFPaper.S2370MapCompSignActual

end
