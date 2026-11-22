import LeanFormal.IUT.Foundations.Theta.GaussianKernel
import LeanFormal.IUT.Foundations.Theta.GaussianSquareSum

/-!
# Mzk1GaussianKernelLawActual — derived laws for the Gaussian theta kernel / square sums
(new theorems from existing tree assets). No copies/bookkeeping, no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GaussianKernelLawActual

open LeanFormal.IUT
open scoped BigOperators

/-- The Gaussian theta value is even in the index. -/
theorem realThetaValue_neg' (q : ℝ) (j : ℤ) :
    realThetaValue q (-j) = realThetaValue q j := by
  unfold realThetaValue
  rw [gaussExponent_neg]

/-- Closed form at index one: q^1. -/
theorem realThetaValue_one (q : ℝ) : realThetaValue q 1 = q := by
  have h : (gaussExponent 1).toNat = 1 := by
    unfold gaussExponent
    norm_num
  unfold realThetaValue
  rw [h]
  exact pow_one q

/-- Closed form at index two: q^4. -/
theorem realThetaValue_two (q : ℝ) : realThetaValue q 2 = q ^ 4 := by
  have h : (gaussExponent 2).toNat = 4 := by
    unfold gaussExponent
    norm_num
  unfold realThetaValue
  rw [h]
  rfl

/-- Closed form at index three: q^9. -/
theorem realThetaValue_three (q : ℝ) : realThetaValue q 3 = q ^ 9 := by
  have h : (gaussExponent 3).toNat = 9 := by
    unfold gaussExponent
    norm_num
  unfold realThetaValue
  rw [h]
  rfl

/-- Recursion for the Gaussian square sums. -/
theorem gaussianSquareSum_succ (n : ℕ) :
    gaussianSquareSum (n + 1) = gaussianSquareSum n + ((n + 1 : ℕ) : ℝ) ^ 2 := by
  unfold gaussianSquareSum
  rw [Finset.sum_range_succ]

#check realThetaValue_neg'
#check realThetaValue_one
#check realThetaValue_two
#check realThetaValue_three
#check gaussianSquareSum_succ

end LeanFormal.IUT.XiFPaper.Mzk1GaussianKernelLawActual
end
