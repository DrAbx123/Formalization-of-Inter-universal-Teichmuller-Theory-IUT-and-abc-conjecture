import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap-2 numeric witness

Concrete instance of the green Gap-2 consumer: regionVolume = ofReal 1,
eps = weight = theta = 0, D = 1.  The named `SNamed` estimate holds by
`ofReal` monotonicity, and `gap2_real_bound` gives the real inequality. -/

namespace LeanFormal.IUT.Objects.ABCBridgeGap2

theorem gap2_numeric_SNamed :
    SNamed (ENNReal.ofReal (1 : Real)) (0 : Real) (0 : Real) (0 : Real) (1 : Real) := by
  unfold SNamed
  norm_num

theorem gap2_numeric_witness :
    (ENNReal.ofReal (1 : Real)).toReal ≤
      (1 + (0 : Real)) * (0 : Real) + (0 : Real) + (1 : Real) := by
  apply gap2_real_bound
  · norm_num
  · exact gap2_numeric_SNamed

end LeanFormal.IUT.Objects.ABCBridgeGap2
