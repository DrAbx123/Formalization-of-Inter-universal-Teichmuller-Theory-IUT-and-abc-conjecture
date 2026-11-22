/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1BadPartArithmeticQpilotActual — bad-part arithmetic (A661)

Arithmetic of the bad-part scaling product: norm multiplicative over finite
products, products of `≥ 1` factors are `≥ 1`, and the log of the product is
nonnegative.  These are the arithmetic facts behind the bad-part logarithmic
increment of the scaled hull radius. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1BadPartArithmeticQpilotActual

universe u

open scoped BigOperators

/-- Norm of a finite product is the product of norms (in a normed field). -/
theorem norm_prod_eq {k : Type u} [NormedField k] {ι : Type*} [Fintype ι]
    (f : ι → k) : ‖∏ i, f i‖ = ∏ i, ‖f i‖ := norm_prod Finset.univ f

/-- A product of `≥ 1` factors is `≥ 1`. -/
theorem one_le_prod_of_one_le {ι : Type*} [Fintype ι] (g : ι → Real)
    (hg : ∀ i, 1 ≤ g i) : 1 ≤ ∏ i, g i := by
  exact Finset.one_le_prod (fun i _ => hg i)

/-- Log of a product of `≥ 1` factors is nonnegative. -/
theorem log_prod_nonneg {ι : Type*} [Fintype ι] (g : ι → Real)
    (hg : ∀ i, 1 ≤ g i) : 0 ≤ Real.log (∏ i, g i) := by
  apply Real.log_nonneg
  exact one_le_prod_of_one_le g hg

/-- Bad-part sum of log-norms is nonnegative when every factor is `≥ 1`. -/
theorem sum_log_nonneg {ι : Type*} [Fintype ι] (g : ι → Real)
    (hg : ∀ i, 1 ≤ g i) : 0 ≤ ∑ i, Real.log (g i) := by
  exact Finset.sum_nonneg (fun i _ => Real.log_nonneg (hg i))

/-- With `g_i = ‖λ_i‖` and `‖λ_i‖ ≥ 1`, the bad-part log product is nonnegative. -/
theorem badPart_log_prod_nonneg {k : Type u} [NormedField k] {ι : Type*}
    [Fintype ι] (lam : ι → k) (hlam : ∀ i, 1 ≤ ‖lam i‖) :
    0 ≤ Real.log (∏ i, ‖lam i‖) := by
  apply Real.log_nonneg
  exact one_le_prod_of_one_le (fun i => ‖lam i‖) hlam

/-- Rows for the bad-part arithmetic. -/
def badPartArithmeticRows : List (String × String) :=
  [ ("norm of product = product of norms", "PROVED"),
    ("product of >= 1 factors is >= 1", "PROVED"),
    ("log product >= 0", "PROVED"),
    ("sum of log-norms >= 0", "PROVED") ]

theorem badPartArithmeticRows_length : badPartArithmeticRows.length = 4 := rfl

#check norm_prod_eq
#check badPart_log_prod_nonneg
#check badPartArithmeticRows_length

end LeanFormal.IUT.XiFPaper.Mzk1BadPartArithmeticQpilotActual
end
