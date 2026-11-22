import LeanFormal.IUT.Foundations.Theta.OddTheta

/-!
# Mzk1OddThetaExponentValueActual — concrete values of the odd theta exponent
(new closed-form theorems from the existing oddThetaExponent definition).
No copies/bookkeeping; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1OddThetaExponentValueActual

open LeanFormal.IUT.Foundations.Theta

/-- Derived: exponent at 0. -/
theorem oddThetaExponent_zero_value : oddThetaExponent 0 = 0 := by
  unfold oddThetaExponent
  norm_num

/-- Derived: exponent at 1. -/
theorem oddThetaExponent_one_value : oddThetaExponent 1 = 1 := by
  unfold oddThetaExponent
  norm_num

/-- Derived: exponent at 2. -/
theorem oddThetaExponent_two_value : oddThetaExponent 2 = 3 := by
  unfold oddThetaExponent
  norm_num

/-- Derived: exponent at 3. -/
theorem oddThetaExponent_three_value : oddThetaExponent 3 = 6 := by
  unfold oddThetaExponent
  norm_num

/-- Derived: exponent at -1. -/
theorem oddThetaExponent_neg_one_value : oddThetaExponent (-1) = 0 := by
  unfold oddThetaExponent
  norm_num

/-- Derived: exponent at -2. -/
theorem oddThetaExponent_neg_two_value : oddThetaExponent (-2) = 1 := by
  unfold oddThetaExponent
  norm_num

/-- Derived: exponent at -3. -/
theorem oddThetaExponent_neg_three_value : oddThetaExponent (-3) = 3 := by
  unfold oddThetaExponent
  norm_num

#check oddThetaExponent_zero_value
#check oddThetaExponent_one_value
#check oddThetaExponent_two_value
#check oddThetaExponent_three_value
#check oddThetaExponent_neg_one_value
#check oddThetaExponent_neg_two_value
#check oddThetaExponent_neg_three_value

end LeanFormal.IUT.XiFPaper.Mzk1OddThetaExponentValueActual
end
