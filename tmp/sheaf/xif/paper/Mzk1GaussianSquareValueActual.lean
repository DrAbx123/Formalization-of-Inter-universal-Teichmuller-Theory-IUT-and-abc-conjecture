import LeanFormal.IUT.Foundations.Theta.GaussianSquareSum

/-!
# Mzk1GaussianSquareValueActual — concrete values of the Gaussian square sums
(new closed-form value theorems from the existing asset). No copies/bookkeeping.
No axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GaussianSquareValueActual

open LeanFormal.IUT

/-- Derived value: gaussianSquareSum 0 = 0. -/
theorem gaussianSquareSum_zero_value : gaussianSquareSum 0 = 0 := by
  have h := gaussianSquareSum_formula 0
  norm_num at h
  exact h

/-- Derived value: gaussianSquareSum 1 = 1. -/
theorem gaussianSquareSum_one_value : gaussianSquareSum 1 = 1 := by
  have h := gaussianSquareSum_formula 1
  norm_num at h
  exact h

/-- Derived value: gaussianSquareSum 2 = 5. -/
theorem gaussianSquareSum_two_value : gaussianSquareSum 2 = 5 := by
  have h := gaussianSquareSum_formula 2
  norm_num at h
  exact h

/-- Derived value: gaussianSquareSum 3 = 14. -/
theorem gaussianSquareSum_three_value : gaussianSquareSum 3 = 14 := by
  have h := gaussianSquareSum_formula 3
  norm_num at h
  exact h

/-- Derived value: gaussianSquareSum 4 = 30. -/
theorem gaussianSquareSum_four_value : gaussianSquareSum 4 = 30 := by
  have h := gaussianSquareSum_formula 4
  norm_num at h
  exact h

/-- Derived: the concrete values also follow from the closed formula. -/
theorem gaussianSquareSum_three_via_formula :
    gaussianSquareSum 3 = (3 : ℝ) * (3 + 1) * (2 * 3 + 1) / 6 :=
  gaussianSquareSum_formula 3

#check gaussianSquareSum_zero_value
#check gaussianSquareSum_one_value
#check gaussianSquareSum_two_value
#check gaussianSquareSum_three_value
#check gaussianSquareSum_four_value
#check gaussianSquareSum_three_via_formula

end LeanFormal.IUT.XiFPaper.Mzk1GaussianSquareValueActual
end
