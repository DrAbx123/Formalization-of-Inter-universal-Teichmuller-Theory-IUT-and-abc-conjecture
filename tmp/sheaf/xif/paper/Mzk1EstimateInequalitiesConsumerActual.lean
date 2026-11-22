import tmp.sheaf.xif.paper.Mzk1EstimateInequalitiesActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1EstimateInequalitiesConsumerActual — elementary estimate bookkeeping bundle

Reuses the EXIT0 elementary inequalities (square nonneg, 2ab <= a^2+b^2,
ab <= (a^2+b^2)/2, (a+b)^2 <= 2(a^2+b^2)) as a named bundle with projections.
No new math; no closure; gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1EstimateInequalitiesConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1EstimateInequalitiesActual

structure EstimateInequalitiesBundle : Prop where
  square_nonneg : ∀ x : ℚ, 0 ≤ x ^ 2
  two_mul_le : ∀ a b : ℚ, 2 * a * b ≤ a ^ 2 + b ^ 2
  mul_le_half : ∀ a b : ℚ, a * b ≤ (a ^ 2 + b ^ 2) / 2
  sq_add_le : ∀ a b : ℚ, (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2)

def estimateInequalitiesBundle : EstimateInequalitiesBundle :=
{ square_nonneg := square_nonneg_bookkeeping
  two_mul_le := two_mul_le_sq_add_sq
  mul_le_half := mul_le_half_sq_add_sq
  sq_add_le := sq_add_le_two_sq_add_sq }

theorem estimateBundle_two_mul_le (a b : ℚ) : 2 * a * b ≤ a ^ 2 + b ^ 2 :=
  estimateInequalitiesBundle.two_mul_le a b

theorem estimateBundle_mul_le_half (a b : ℚ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 :=
  estimateInequalitiesBundle.mul_le_half a b

def estimateInequalitiesRows : List (String × String × String) :=
  [ ("bundle", "EstimateInequalitiesBundle", "DEF (reuses EXIT0 inequalities)"),
    ("projections", "estimateBundle_two_mul_le / estimateBundle_mul_le_half", "PROVED"),
    ("scope", "elementary bookkeeping; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem estimateInequalitiesRows_length : estimateInequalitiesRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1EstimateInequalitiesConsumerActual

end
