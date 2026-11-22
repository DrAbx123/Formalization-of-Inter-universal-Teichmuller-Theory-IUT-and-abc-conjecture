import tmp.sheaf.xif.paper.Mzk1B5FullProductFormulaActual
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic

/-! # B5 full product formula in count-weighted form

For x : O_K, x ≠ 0:
  sum_finite log(w x) = - sum_v count_v(span{x}) log absNorm(v)
and combining with the full product formula:
  sum_arch w.mult log(w x) = sum_v count_v(span{x}) log absNorm(v).
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5FullProductFormulaCountActual

open NumberField

variable (K : Type) [Field K] [NumberField K]

/-- Finite-place log sum of a principal integral element is minus the count sum. -/
theorem finite_log_sum_eq_neg_count_sum
    (x : NumberField.RingOfIntegers K) (hx : x ≠ 0) :
    (∑ᶠ w : NumberField.FinitePlace K,
        Real.log (w (x : K))) =
      - (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {x})).factors : Real) *
            Real.log (Ideal.absNorm v.asIdeal : Real)) := by
  classical
  have hxK : (x : K) ≠ 0 := by
    exact_mod_cast hx
  have hspan_ne : Ideal.span ({x} : Set (NumberField.RingOfIntegers K)) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hx
  have hprod := NumberField.FinitePlace.prod_eq_inv_abs_norm_int (K := K) hx
  have hlog := congrArg Real.log hprod
  rw [Real.log_finprod (fun w : NumberField.FinitePlace K =>
    NumberField.FinitePlace.pos_iff.mpr hxK)] at hlog
  rw [Real.log_inv] at hlog
  have hnorm_eq : |((Algebra.norm Int x : Int) : Real)| =
      (Ideal.absNorm (Ideal.span ({x} : Set (NumberField.RingOfIntegers K))) : Real) := by
    rw [Ideal.absNorm_span_singleton]
    norm_num [Int.natCast_natAbs, Int.cast_abs]
  rw [hnorm_eq] at hlog
  rw [Mzk1B5LocalGlobalProductFormulaActual.log_absNorm_eq_sum_count_mul_log K
    (Ideal.span ({x} : Set (NumberField.RingOfIntegers K))) hspan_ne] at hlog
  exact hlog

/-- Count-weighted full product formula: archimedean log sum equals finite count sum. -/
theorem arch_log_eq_count_sum
    (x : NumberField.RingOfIntegers K) (hx : x ≠ 0) :
    (∑ w : NumberField.InfinitePlace K, (w.mult : Real) * Real.log (w (x : K))) =
      ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {x})).factors : Real) *
          Real.log (Ideal.absNorm v.asIdeal : Real) := by
  have hfull := Mzk1B5FullProductFormulaActual.full_product_formula_log K (x := (x : K)) (by
    exact_mod_cast hx)
  rw [finite_log_sum_eq_neg_count_sum K x hx] at hfull
  linear_combination hfull

#check finite_log_sum_eq_neg_count_sum
#check arch_log_eq_count_sum
end LeanFormal.IUT.XiFPaper.Mzk1B5FullProductFormulaCountActual
end
