import tmp.sheaf.xif.paper.S2312EqualizerIsoFinal2Actual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2312EqualizerIsoFinal2Actual
open LeanFormal.IUT.XiFPaper.S2285RMapNatActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S2206PConstantSheafActual
open LeanFormal.IUT.XiFPaper.S2192QHomSheavesActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2316NatIsoProofActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))

-- The final NatIso naturality is not closed.  After ext x and cases x, the
-- zero/one goals still contain the composite components
-- (eqToIso ≪≫ limitObjIsoLimitCompEvaluation ≪≫ isoOfNatIso ≪≫ equalizerIso).symm
-- and the pullHom restriction, and rfl/rw [S2285f_natural] do not apply.
#check S2312QHomEqualizerObjIso
#check S2271QHomObj_eq_subtype
#check S2285f_natural
#check S2285R_map_apply

end LeanFormal.IUT.XiFPaper.S2316NatIsoProofActual

end
