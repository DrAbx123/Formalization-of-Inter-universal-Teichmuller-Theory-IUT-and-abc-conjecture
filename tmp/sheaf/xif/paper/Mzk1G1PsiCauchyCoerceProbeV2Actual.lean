/- Unique-named coercion probe (kurt): determine the additive NNReal-norm coercion lemma
available for C and the div_le_self parameter order. Diagnostic only.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
open scoped NNReal

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyCoerceProbeV2Actual

theorem coerce_A (z : ℂ) : (‖z‖₊ : ℝ) = ‖z‖ := coe_nnnorm z

theorem coerce_B (z : ℂ) : (‖z‖₊ : ℝ) = ‖z‖ := by
  rw [← NNReal.coe_nnnorm]
  rfl

theorem divle_A {a b : ℝ≥0} (h : 1 ≤ b) : a / b ≤ a :=
  div_le_self (zero_le a) h

#print axioms coerce_A
#print axioms coerce_B
#print axioms divle_A

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyCoerceProbeV2Actual
end