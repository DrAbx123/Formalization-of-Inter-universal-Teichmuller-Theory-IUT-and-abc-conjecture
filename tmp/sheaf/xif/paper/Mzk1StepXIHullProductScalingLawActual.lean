import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi hull product scaling law

Product law: if every coordinate measure is scaled by the same factor `c`, the
product measure is scaled by `c ^ card`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIHullProductScalingLawActual

theorem prod_scaling_law {ι : Type*} [Fintype ι] (f g : ι → ENNReal)
    (c : ENNReal) (h : ∀ i, f i = c * g i) :
    (∏ i, f i) = c ^ (Fintype.card ι) * ∏ i, g i := by
  calc ∏ i, f i = ∏ i, c * g i := by
        exact Finset.prod_congr rfl (fun i _ => h i)
    _ = (∏ i, (c : ENNReal)) * ∏ i, g i := Finset.prod_mul_distrib
    _ = c ^ (Fintype.card ι) * ∏ i, g i := by
        rw [Finset.prod_const, Finset.card_univ]

theorem prod_scaling_law_one {ι : Type*} [Fintype ι] (g : ι → ENNReal)
    (c : ENNReal) :
    (∏ i, c * g i) = c ^ (Fintype.card ι) * ∏ i, g i :=
  prod_scaling_law (fun i => c * g i) g c (fun _ => rfl)

end LeanFormal.IUT.XiFPaper.Mzk1StepXIHullProductScalingLawActual

end
