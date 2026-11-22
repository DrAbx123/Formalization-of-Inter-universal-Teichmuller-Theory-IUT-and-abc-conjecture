import tmp.sheaf.xif.paper.Mzk1B5LocalGlobalProductFormulaActual
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic

/-! # B5 full product formula (finite + archimedean)

Mathlib has the multiplicative product formula
  (∏ w : NumberField.InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : NumberField.FinitePlace K, w x = 1.
Taking logs gives the additive full product formula
  (∑ w : NumberField.InfinitePlace K, w.mult * log (w x)) +
    (∑ᶠ w : NumberField.FinitePlace K, log (w x)) = 0.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5FullProductFormulaActual

open NumberField

variable (K : Type) [Field K] [NumberField K]

/-- Additive full product formula: archimedean plus finite place log sum is zero. -/
theorem full_product_formula_log {x : K} (hx : x ≠ 0) :
    (∑ w : NumberField.InfinitePlace K, (w.mult : Real) * Real.log (w x)) +
      (∑ᶠ w : NumberField.FinitePlace K, Real.log (w x)) = 0 := by
  have hprod := NumberField.prod_abs_eq_one (K := K) hx
  have hlog := congrArg Real.log hprod
  rw [Real.log_one] at hlog
  have harch_pos : 0 < ∏ w : NumberField.InfinitePlace K, w x ^ w.mult := by
    apply Finset.prod_pos
    intro w _
    exact pow_pos (NumberField.InfinitePlace.pos_iff.mpr hx) _
  have hfin_pos : 0 < ∏ᶠ w : NumberField.FinitePlace K, w x := by
    classical
    rw [finprod_def]
    split_ifs with h
    · apply Finset.prod_pos
      intro w _
      exact NumberField.FinitePlace.pos_iff.mpr hx
    · norm_num
  rw [Real.log_mul harch_pos.ne' hfin_pos.ne'] at hlog
  rw [Real.log_finprod (fun w : NumberField.FinitePlace K => NumberField.FinitePlace.pos_iff.mpr hx)] at hlog
  rw [Real.log_prod (fun w _ => (pow_pos (NumberField.InfinitePlace.pos_iff.mpr hx) _).ne')] at hlog
  simp only [Real.log_pow] at hlog
  exact hlog

#check full_product_formula_log
end LeanFormal.IUT.XiFPaper.Mzk1B5FullProductFormulaActual
end
