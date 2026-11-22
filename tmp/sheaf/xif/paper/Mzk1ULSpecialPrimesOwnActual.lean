/- Own proof of the special-primes numeric bound (replaces the sorryAx-bearing donor
`Mzk1ULSpecialPrimesNumericActual.specialPrimes_log_sum_le`).

bound: Sum_{p in {2,3,5,l}} log p <= 5 + log l, from log 2 + log 3 + log 5 = log 30
<= log 32 = 5 log 2 <= 5 (Real.log_pow / log_le_sub_one_of_pos).  Reuse:
`Mzk1ULSQPaperActual.specialPrimes` (= {2,3,5,l.value}).
-/
import tmp.sheaf.xif.paper.Mzk1ULSQPaperActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULSpecialPrimesOwnActual

open LeanFormal.IUT

/-- PROVED: log 2 + log 3 + log 5 <= 5. -/
theorem log_two_three_five_le_five : Real.log 2 + Real.log 3 + Real.log 5 ≤ 5 := by
  have h30 : Real.log 2 + Real.log 3 + Real.log 5 = Real.log 30 := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [h30]
  have h1 : Real.log 30 ≤ Real.log 32 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have h3 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  linarith

/-- PROVED: the special-primes log sum is <= 5 + log l. -/
theorem specialPrimes_log_sum_le_own (l : PrimeGeFive) :
    (∑ p ∈ Mzk1ULSQPaperActual.specialPrimes l, Real.log (p : ℝ))
      ≤ 5 + Real.log (l.value : ℝ) := by
  have hl5 : (2 : ℝ) < (l.value : ℝ) := by
    have : (2 : ℕ) < l.value := by have := l.ge_five; omega
    exact_mod_cast this
  have hdist : l.value ≠ 2 := by have h := l.ge_five; omega
  have hdist3 : l.value ≠ 3 := by have h := l.ge_five; omega
  -- split on whether l equals 5 (then the set collapses to {2,3,5})
  by_cases h5 : l.value = 5
  · have h5' : ((5 : ℕ) : ℝ) = (l.value : ℝ) := by exact_mod_cast h5.symm
    have hsum : (∑ p ∈ Mzk1ULSQPaperActual.specialPrimes l, Real.log (p : ℝ))
        = Real.log 2 + Real.log 3 + Real.log 5 := by
      simp [Mzk1ULSQPaperActual.specialPrimes, h5]
      ring
    rw [hsum, ← h5']
    push_cast
    have hlog5 : (0 : ℝ) ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    linarith [log_two_three_five_le_five, hlog5]
  · have hlne : l.value ≠ 2 ∧ l.value ≠ 3 ∧ l.value ≠ 5 := by
      refine ⟨hdist, ?_, h5⟩
      intro h3; have hge := l.ge_five; omega
    have hset : Mzk1ULSQPaperActual.specialPrimes l = ({2, 3, 5, l.value} : Finset ℕ) := by
      simp [Mzk1ULSQPaperActual.specialPrimes]
    rw [hset]
    have h2not : (2 : ℕ) ∉ ({3, 5, l.value} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have h3not : (3 : ℕ) ∉ ({5, l.value} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have h5not : (5 : ℕ) ∉ ({l.value} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      omega
    rw [Finset.sum_insert h2not, Finset.sum_insert h3not, Finset.sum_insert h5not,
      Finset.sum_singleton]
    push_cast
    linarith [log_two_three_five_le_five]

end LeanFormal.IUT.XiFPaper.Mzk1ULSpecialPrimesOwnActual
end