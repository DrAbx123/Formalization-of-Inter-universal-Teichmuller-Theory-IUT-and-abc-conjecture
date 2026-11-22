import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import Mathlib.Tactic.Linarith

/-!
# The real bound in IUT IV Proposition 1.4(iii)

This is the last numerical step used by Theorem 1.10(v), after the actual
normalization-region log-volume has been bounded by `(-m + b_I) * log p`.
The exponent is the single floor `m = floor (lambda - d_I - a_I)`.

The local exponents and their estimates are reused from
`IntegralLogShellSharpBounds`. No lattice inclusion, Kummer comparison, or
source-level volume claim is asserted in this file.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LocalFieldLogarithm
open scoped BigOperators

variable {Index : Type*} [Fintype Index]

/-- Outside the exceptional set the two paper exponents cancel exactly.
Thus only the exceptional indices contribute to the correction term. -/
theorem stepVPaperCorrectionSum_le
    {p : ℕ} (prime_isPrime : p.Prime)
    (ramification : Index → ℕ) (ramification_pos : ∀ index, 1 ≤ ramification index)
    (exceptional : Finset Index)
    (small_outside : ∀ index, index ∉ exceptional → ramification index ≤ p - 2) :
    ((∑ index, logShellPaperAExponent p (ramification index)) +
        ∑ index, logShellPaperBExponent p (ramification index)) * Real.log (p : ℝ) ≤
      ∑ index ∈ exceptional, (3 + Real.log (ramification index : ℝ)) := by
  classical
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  calc
    ∑ index, (logShellPaperAExponent p (ramification index) +
        logShellPaperBExponent p (ramification index)) * Real.log (p : ℝ) =
        ∑ index ∈ exceptional, (logShellPaperAExponent p (ramification index) +
          logShellPaperBExponent p (ramification index)) * Real.log (p : ℝ) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ exceptional)
      intro index _ index_not_exceptional
      have ramification_small := small_outside index index_not_exceptional
      have prime_ne_two : p ≠ 2 := by
        intro prime_eq_two
        have ramification_positive := ramification_pos index
        omega
      rw [logShellPaperAExponent_add_logShellPaperBExponent_eq_zero_of_small
        prime_isPrime prime_ne_two (ramification_pos index) ramification_small, zero_mul]
    _ ≤ ∑ index ∈ exceptional, (3 + Real.log (ramification index : ℝ)) :=
      Finset.sum_le_sum fun index _ =>
        logShellPaperExponent_sum_mul_log_le_three_add_log
          prime_isPrime (ramification_pos index)

/-- The exact paper constant: one joint floor costs at most `log p`, and
the remaining local correction is supported on the exceptional set.

`lambda` and the different orders can be arbitrary real numbers; neither
a sign condition on `lambda` nor a separate rounding of the sums is used.
The preceding geometric estimate is the responsibility of the consumer. -/
theorem stepVPaperLogVolumeBound
    {p : ℕ} (prime_isPrime : p.Prime)
    (ramification : Index → ℕ) (ramification_pos : ∀ index, 1 ≤ ramification index)
    (differentOrder : Index → ℝ) (lambda : ℝ)
    (exceptional : Finset Index)
    (small_outside : ∀ index, index ∉ exceptional → ramification index ≤ p - 2) :
    (-((⌊lambda - (∑ index, differentOrder index) -
          ∑ index, logShellPaperAExponent p (ramification index)⌋ : ℤ) : ℝ) +
        ∑ index, logShellPaperBExponent p (ramification index)) * Real.log (p : ℝ) ≤
      (-lambda + (∑ index, differentOrder index) + 1) * Real.log (p : ℝ) +
        ∑ index ∈ exceptional, (3 + Real.log (ramification index : ℝ)) := by
  have floor_bound := Int.lt_floor_add_one
    (lambda - (∑ index, differentOrder index) -
      ∑ index, logShellPaperAExponent p (ramification index))
  have rounding_bound :
      -((⌊lambda - (∑ index, differentOrder index) -
          ∑ index, logShellPaperAExponent p (ramification index)⌋ : ℤ) : ℝ) +
          ∑ index, logShellPaperBExponent p (ramification index) ≤
        (-lambda + (∑ index, differentOrder index) + 1) +
          ((∑ index, logShellPaperAExponent p (ramification index)) +
            ∑ index, logShellPaperBExponent p (ramification index)) := by
    linarith
  have log_nonnegative : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast prime_isPrime.one_lt.le)
  calc
    _ ≤ ((-lambda + (∑ index, differentOrder index) + 1) +
        ((∑ index, logShellPaperAExponent p (ramification index)) +
          ∑ index, logShellPaperBExponent p (ramification index))) * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_right rounding_bound log_nonnegative
    _ = (-lambda + (∑ index, differentOrder index) + 1) * Real.log (p : ℝ) +
        ((∑ index, logShellPaperAExponent p (ramification index)) +
          ∑ index, logShellPaperBExponent p (ramification index)) * Real.log (p : ℝ) :=
      add_mul _ _ _
    _ ≤ _ := _root_.add_le_add (le_refl _)
      (stepVPaperCorrectionSum_le prime_isPrime ramification ramification_pos
        exceptional small_outside)

end LeanFormal.IUT.NumberFieldFinitePlace
