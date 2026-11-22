import tmp.sheaf.xif.paper.S2312EqualizerIsoFinal2Actual
import Mathlib.CategoryTheory.Limits.Types.Equalizers

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2312EqualizerIsoFinal2Actual
open LeanFormal.IUT.XiFPaper.S2308EqualizerIsoFinalActual
open LeanFormal.IUT.XiFPaper.S2303EvalDiagramProofActual
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

namespace LeanFormal.IUT.XiFPaper.S2320NatIsoCastActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
variable (T : (Over S)ᵒᵖ)

-- Cast API available for the component decomposition:
#check Limits.Types.equalizerIso_hom_comp_subtype
#check Limits.Types.equalizerIso_inv_comp_ι
#check limit.isoLimitCone_inv_π
#check S2312QHomEqualizerObjIso
#check S2312EqualizerSubtypeIso
#check S2308EqualizerObjIso
#check S2303EvalDiagramIso

-- The remaining cast goal is: after composing the naturality square with
-- Types.equalizerIso.hom at T2 and applying Subtype.ext, the component hom
-- should reduce to the subtype value of the Q hom element.  This reduction was
-- not completed; rfl/simp do not eliminate the eqToIso/limit.isoLimitCone casts.

end LeanFormal.IUT.XiFPaper.S2320NatIsoCastActual

end
