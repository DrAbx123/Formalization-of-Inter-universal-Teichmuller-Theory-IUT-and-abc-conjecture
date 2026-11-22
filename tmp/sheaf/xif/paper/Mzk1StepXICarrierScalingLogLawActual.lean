import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi carrier scaling log law

Log law for carrier product scaling: log of a uniformly scaled product equals
card·log c plus the log of the original product. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICarrierScalingLogLawActual

theorem carrier_log_scaling_law {ι : Type*} [Fintype ι]
    (f : ι → Real) (c : Real) (hc : 0 < c)
    (hf : ∀ i, 0 < f i) :
    Real.log (∏ i, c * f i) =
      (Fintype.card ι : Real) * Real.log c + Real.log (∏ i, f i) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [Real.log_mul (by positivity) (Finset.prod_pos fun i _ => hf i)]
  rw [Real.log_pow]
  ring

theorem carrier_log_scaling_law_abs {ι : Type*} [Fintype ι]
    (f : ι → Real) {c : Real} (hc : 0 < c)
    (hf : ∀ i, 0 < f i) :
    Real.log (∏ i, c * f i) =
      Real.log (c ^ (Fintype.card ι)) + Real.log (∏ i, f i) := by
  rw [← Real.log_pow]
  exact carrier_log_scaling_law f c hc hf

end LeanFormal.IUT.XiFPaper.Mzk1StepXICarrierScalingLogLawActual

end
