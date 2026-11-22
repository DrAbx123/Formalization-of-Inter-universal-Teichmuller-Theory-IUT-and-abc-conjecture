/- hspecial: specialPrimes l = {2,3,5,l.value} 的 log 和 ≤ 5 + log l。
  l 素数且 ≥5 ⇒ 只有 l=5 时出现重复（集合去重），否则四个 prime 互异。
  donor: Mzk1ULStepHiiHsQActual.log_thirty_le_five/log_thirty_mul_le（DONE 19:04:09）;
  Mzk1ULSQPaperActual.specialPrimes。 -/
import tmp.sheaf.xif.paper.Mzk1ULSQPaperActual
import tmp.sheaf.xif.paper.Mzk1ULStepHiiHsQActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULSpecialPrimesNumericActual

open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULStepHiiHsQActual

/-- log2+log3+log5 = log30。 -/
theorem log_two_three_five :
    Real.log (2 : ℝ) + Real.log (3 : ℝ) + Real.log (5 : ℝ) = Real.log (30 : ℝ) := by
  rw [← Real.log_mul (by norm_num) (by norm_num),
    ← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

/-- hspecial: Σ_{p∈specialPrimes l} log p ≤ 5 + log l（l≥5 prime）。 -/
theorem specialPrimes_log_sum_le (l : PrimeGeFive) :
    (∑ p ∈ specialPrimes l, Real.log (p : ℝ)) ≤ 5 + Real.log (l.value : ℝ) := by
  have hl5 : (5 : ℕ) ≤ l.value := l.ge_five
  have hlpos : (0 : ℝ) < (l.value : ℝ) := by exact_mod_cast l.prime.pos
  have h2 : l.value ≠ 2 := by omega
  have h3 : l.value ≠ 3 := by omega
  by_cases h5 : l.value = 5
  · simp only [specialPrimes, h5, Finset.insert_eq, Finset.mem_singleton,
      Finset.sum_insert, Finset.sum_empty] at *
    rw [log_two_three_five]
    have h : Real.log (30 : ℝ) ≤ 5 := log_thirty_le_five
    have hlog5 : (0 : ℝ) ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  · have hsum : (∑ p ∈ specialPrimes l, Real.log (p : ℝ)) =
        Real.log (2 : ℝ) + Real.log (3 : ℝ) + Real.log (5 : ℝ) + Real.log (l.value : ℝ) := by
      simp [specialPrimes, h2, h3, h5, add_assoc]
    rw [hsum, log_two_three_five]
    exact log_thirty_mul_le hlpos

#print axioms log_two_three_five
#print axioms specialPrimes_log_sum_le

end LeanFormal.IUT.XiFPaper.Mzk1ULSpecialPrimesNumericActual
