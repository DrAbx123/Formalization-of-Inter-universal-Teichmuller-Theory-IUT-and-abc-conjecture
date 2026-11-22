import tmp.sheaf.xif.paper.S2393StrictSignActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2393StrictSignActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2259QMapPrecompActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2421StrictSign2Actual

variable {A B C : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ}
variable (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (hh : f ≫ g = h)
variable (M : S2152Q.obj A)

-- Exact #check output:
-- (S2152Q.mapComp' f g h hh).hom.toNatTrans.app M :
--   { f_1 //
--     (actionAsFunctor SignGroup (unop C.as ⟶ S1726AffineOver)).map f_1
--       ((S2152Q.map h).toFunctor.obj M).snd
--     = ((S2152Q.map f ≫ S2152Q.map g).toFunctor.obj M).snd }
--
-- This is an action-category hom subtype, but its .val is elaborated at a
-- base-Type function type, not at SignGroup.  Therefore the intended
-- .val = 1 statement is still ill-typed; a type ascription to the action
-- category hom is needed.  The identity of the Iso.refl mapComp' coherence was
-- not extracted.
#check (S2152Q.mapComp' f g h hh).hom.toNatTrans.app M
#check S1971PrecompFunctor_map_val
#check S2259QMapPrecomp

end LeanFormal.IUT.XiFPaper.S2421StrictSign2Actual

end
