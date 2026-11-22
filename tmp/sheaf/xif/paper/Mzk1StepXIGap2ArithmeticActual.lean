import tmp.sheaf.xif.paper.Mzk1StepXIGap2ShapeDecompositionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap2 arithmeticization

Rearranged arithmetic forms of the named Gap2 estimate. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ArithmeticActual

open LeanFormal.IUT.Objects.ABCBridgeGap2
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ShapeDecompositionActual

theorem gap2_arithmetic_real (S : Gap2Shape)
    (hR : 0 ≤ (1 + S.eps) * S.weight + S.theta + S.D) :
    S.regionVolume.toReal - (1 + S.eps) * S.weight ≤ S.theta + S.D :=
  by linarith [gap2_shape_real S hR]

theorem gap2_arithmetic_ennreal (S : Gap2Shape) :
    S.regionVolume ≤ ENNReal.ofReal ((1 + S.eps) * S.weight + S.theta + S.D) :=
  gap2_shape_named S

theorem gap2_arithmetic_zero_eps (S : Gap2Shape)
    (hR : 0 ≤ S.weight + S.theta + S.D) :
    S.regionVolume.toReal ≤ S.weight + S.theta + S.D :=
  by simpa using gap2_shape_real S (by simpa using hR)

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ArithmeticActual

end
