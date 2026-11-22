import tmp.sheaf.xif.paper.S2312EqualizerIsoFinal2Actual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2312EqualizerIsoFinal2Actual
open LeanFormal.IUT.XiFPaper.S2285RMapNatActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S2206PConstantSheafActual
open LeanFormal.IUT.XiFPaper.S2192QHomSheavesActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2313NatIsoFinalActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))

-- The final NatIso naturality is not closed.  After ext x and cases x the two
-- remaining goals are:
--
-- zero:
--   (Fork.ι Types.equalizerLimit.cone)
--     (pullHom x (p.unop.left) ...) = (S2206P0 S).map p ((Fork.ι ...) x)
--
-- one:
--   (S2285f S M).app T2 ((Fork.ι ...) (pullHom x ...))
--     = (S2192R S).map p ((S2285f S M).app T1 ((Fork.ι ...) x))
#check S2312EqualizerSubtypeIso
#check S2312QHomEqualizerObjIso
#check S2271QHomObj_eq_subtype
#check S2285f_natural

end LeanFormal.IUT.XiFPaper.S2313NatIsoFinalActual

end
