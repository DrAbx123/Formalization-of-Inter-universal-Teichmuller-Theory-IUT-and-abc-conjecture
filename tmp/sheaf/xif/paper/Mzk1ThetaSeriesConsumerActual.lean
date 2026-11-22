import LeanFormal.IUT.Foundations.Theta.GaussianKernel
import LeanFormal.IUT.Foundations.Theta.GaussianSquareSum

/-!
# Mzk1ThetaSeriesConsumerActual — consumer theorems over the tree theta/Gaussian assets
(GaussianKernel/GaussianSquareSum, OLEAN_FRESH). Composed projections only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaSeriesConsumerActual

open LeanFormal.IUT

/-- Consumer: Gaussian theta value at 0 is 1. -/
theorem consumer_realThetaValue_zero (q : ℝ) : realThetaValue q 0 = 1 :=
  realThetaValue_zero q

/-- Consumer: Gaussian theta values are positive for q > 0. -/
theorem consumer_realThetaValue_pos {q : ℝ} (hq : 0 < q) (j : ℤ) :
    0 < realThetaValue q j :=
  realThetaValue_pos hq j

/-- Consumer: the Gaussian exponent is nonnegative. -/
theorem consumer_gaussExponent_nonneg (j : ℤ) : 0 ≤ gaussExponent j :=
  gaussExponent_nonneg j

/-- Consumer: Gaussian square-sum closed formula. -/
theorem consumer_gaussianSquareSum (n : ℕ) :
    gaussianSquareSum n = (n : ℝ) * (n + 1) * (2 * n + 1) / 6 :=
  gaussianSquareSum_formula n

/-- Consumer: normalized Gaussian degree factor formula for odd l >= 5. -/
theorem consumer_normalizedGaussianDegree (l : ℕ) (hodd : Odd l) (hl5 : 5 ≤ l) :
    normalizedGaussianDegree l = (l : ℝ) * (l + 1) / 12 :=
  normalizedGaussianDegree_eq_factor l hodd hl5

#check consumer_realThetaValue_zero
#check consumer_realThetaValue_pos
#check consumer_gaussExponent_nonneg
#check consumer_gaussianSquareSum
#check consumer_normalizedGaussianDegree

end LeanFormal.IUT.XiFPaper.Mzk1ThetaSeriesConsumerActual
end
