import tmp.sheaf.xif.paper.S2332PsubCorrectActual
import tmp.sheaf.xif.paper.S2386MapCompSign2Actual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2332PsubCorrectActual
open LeanFormal.IUT.XiFPaper.S2386MapCompSign2Actual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2259QMapPrecompActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2393StrictSignActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))

-- Strict route status:
-- Unfolding S2152Q = S2152PFunctor.toPseudofunctor' exposes the strict
-- pseudofunctor whose mapComp is Iso.refl.  After unfolding, the sign-projection
-- goal is of the form
--   ↑((mapComp' ...).hom.toNatTrans.app M
--       ≫ (S1971PrecompFunctor ...).toCatHom.toFunctor.map x
--       ≫ (mapComp' ...).inv.toNatTrans.app N) = ↑x
-- with mapComp' built from Iso.refl coherences.  The missing step is to show
-- the Iso.refl mapComp' app component acts as the identity functor on the
-- action category, so its sign projection is identity; then
-- S1971PrecompFunctor_map_val gives the middle factor ↑x and the goal closes.
--
-- This reduction was not completed; direct simp produced a large unfolding and
-- did not discharge the mapComp' component.
#check S1971PrecompFunctor_map_val
#check S2259QMapPrecomp
#check S2271QHomObj_eq_subtype
#check S2332Psub

end LeanFormal.IUT.XiFPaper.S2393StrictSignActual

end
