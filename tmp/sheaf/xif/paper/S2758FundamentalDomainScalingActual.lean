import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

noncomputable section
open scoped ENNReal Pointwise
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2758FundamentalDomainScalingActual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Haar volume of a real dilation: `μ (r • s) = |r|^dim * μ s`. -/
theorem S2758_haar_smul (r : Real) (s : Set E) :
    μ (r • s) =
      ENNReal.ofReal (abs (r ^ Module.finrank ℝ E)) * μ s :=
  Measure.addHaar_smul μ r s

/-- Nonnegative-dilation form: no absolute value. -/
theorem S2758_haar_smul_of_nonneg {r : Real} (hr : 0 ≤ r)
    (s : Set E) :
    μ (r • s) =
      ENNReal.ofReal (r ^ Module.finrank ℝ E) * μ s := by
  rw [S2758_haar_smul, abs_of_nonneg (pow_nonneg hr _)]

#check S2758_haar_smul
#check S2758_haar_smul_of_nonneg
#print axioms S2758_haar_smul

end LeanFormal.IUT.XiFPaper.S2758FundamentalDomainScalingActual
end
