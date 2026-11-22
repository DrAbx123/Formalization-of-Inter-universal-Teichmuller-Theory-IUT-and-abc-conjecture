import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2728NormLogProductActual

/-- Positivity of a finite product of positive local norms. -/
theorem S2728_prod_pos {ι : Type*} [Fintype ι] (f : ι → Real)
    (hpos : ∀ i, 0 < f i) : 0 < ∏ i, f i :=
  Finset.prod_pos fun i _ => hpos i

/-- Log of a finite product of positive local factors is the sum of logs. -/
theorem S2728_log_prod {ι : Type*} [Fintype ι] (f : ι → Real)
    (hpos : ∀ i, 0 < f i) :
    Real.log (∏ i, f i) = ∑ i, Real.log (f i) := by
  rw [Real.log_prod]
  intro i _
  exact ne_of_gt (hpos i)

/-- The negative log of a finite product of positive local norms is the sum of
the local negative logs.  This is the algebraic multiplication step for the
global product norm/log carrier. -/
theorem S2728_neg_log_prod {ι : Type*} [Fintype ι] (f : ι → Real)
    (hpos : ∀ i, 0 < f i) :
    -Real.log (∏ i, f i) = ∑ i, -Real.log (f i) := by
  rw [S2728_log_prod f hpos, Finset.sum_neg_distrib]

/-- Equivalent product/exponential form: the product is `exp` of the log sum. -/
theorem S2728_prod_eq_exp_sum_log {ι : Type*} [Fintype ι] (f : ι → Real)
    (hpos : ∀ i, 0 < f i) :
    ∏ i, f i = Real.exp (∑ i, Real.log (f i)) := by
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact (Real.exp_log (hpos i)).symm

#print axioms S2728_neg_log_prod
#print axioms S2728_prod_eq_exp_sum_log

end LeanFormal.IUT.XiFPaper.S2728NormLogProductActual
end
