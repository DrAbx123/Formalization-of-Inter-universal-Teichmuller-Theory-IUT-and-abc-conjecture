/- hsQ λ 数值界（B 表）：用 sophie 的无条件 log s^Q = Σ log p + q/d support 界 + special primes 常数。 -/
import tmp.sheaf.xif.paper.Mzk1ULSQPaperFinalActual
import tmp.sheaf.xif.paper.Mzk1ULHSQFinalActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperFinalActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- 两个 Finset 的 log 和可加性上界（非负项）。 -/
theorem sum_union_log_le_add (s t : Finset ℕ) :
    (∑ p ∈ s ∪ t, Real.log (p : ℝ)) ≤
      (∑ p ∈ s, Real.log (p : ℝ)) + (∑ p ∈ t, Real.log (p : ℝ)) := by
  have h := Finset.sum_union (s₁ := s) (s₂ := t \ s) (f := fun p : ℕ => Real.log (p : ℝ))
    Finset.disjoint_sdiff
  have hunion : s ∪ (t \ s) = s ∪ t := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [hunion] at h
  have hle : (∑ x ∈ t \ s, Real.log (x : ℝ)) ≤ (∑ x ∈ t, Real.log (x : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact (Finset.mem_sdiff.mp hx).1
    · intro x _ _
      exact Real.log_natCast_nonneg x
  linarith

/-- hsQ λ 数值界: log s^Q ≤ 2 d_mod S_ar + 5 + log l。 -/
theorem hsQ_lambda_numeric (dmod S_ar : ℝ)
    (hbad : (∑ p ∈ qSupportPrimes T ∪ dSupportPrimes T, Real.log (p : ℝ)) ≤ 2 * dmod * S_ar)
    (hspecial : (∑ p ∈ specialPrimes l, Real.log (p : ℝ)) ≤ 5 + Real.log (l.value : ℝ)) :
    Real.log (sQPaper T) ≤ 2 * dmod * S_ar + 5 + Real.log (l.value : ℝ) := by
  rw [log_sQPaper_eq_sum_log_paper T]
  have h1 : (∑ p ∈ qSupportPrimes T ∪ dSupportPrimes T ∪ specialPrimes l,
      Real.log (p : ℝ)) ≤
      (∑ p ∈ qSupportPrimes T ∪ dSupportPrimes T, Real.log (p : ℝ)) +
        (∑ p ∈ specialPrimes l, Real.log (p : ℝ)) :=
    sum_union_log_le_add (s := qSupportPrimes T ∪ dSupportPrimes T) (t := specialPrimes l)
  linarith

#print axioms sum_union_log_le_add
#print axioms hsQ_lambda_numeric

end LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericActual