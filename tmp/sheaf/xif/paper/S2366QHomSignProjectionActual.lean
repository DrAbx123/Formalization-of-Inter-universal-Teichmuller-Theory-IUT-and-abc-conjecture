import tmp.sheaf.xif.paper.S2332PsubCorrectActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2332PsubCorrectActual
open LeanFormal.IUT.XiFPaper.S2285RMapNatActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2259QMapPrecompActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2366QHomSignProjectionActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))

-- Sign projection goal after unfolding presheafHom.map and pullHom:
--
--   ↑((mapComp' S2152Q ...).hom.toNatTrans.app M ≫
--       (S2152Q.map (p.unop.left).op.toLoc).toFunctor.map x ≫
--         (mapComp' S2152Q ...).inv.toNatTrans.app N)
--     = ↑x
--
-- The middle factor is covered by S1971PrecompFunctor_map_val after
-- S2259QMapPrecomp; the remaining issue is the sign value of the mapComp'
-- coherence app M/N (both are eqToIso coherences of toPseudofunctor'), which
-- was not reduced to 1 in Lean.
#check S1971PrecompFunctor_map_val
#check S2259QMapPrecomp
#check S2271QHomObj_eq_subtype
#check S2332Psub

end LeanFormal.IUT.XiFPaper.S2366QHomSignProjectionActual

end
