import LeanFormal.IUT.Foundations.Theta.OddThetaNegativeDecay

set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- Translation reindexing of an integer-indexed tsum. -/
theorem tsum_addRight_eq_tsum (f : ℤ → L) (a : ℤ) :
    (∑' n : ℤ, f (n + a)) = ∑' n : ℤ, f n :=
  Equiv.tsum_eq (Equiv.addRight a) f

/-- Pulling a constant factor out of an integer-indexed tsum, then reindexing
the translation. -/
theorem tsum_const_mul_addRight_eq (f : ℤ → L) (c : L) (a : ℤ) :
    (∑' n : ℤ, c * f (n + a)) = c * ∑' n : ℤ, f n := by
  rw [tsum_mul_left, tsum_addRight_eq_tsum]

/-- Two-sided summability of the translated theta family, from the production
two-sided summability theorem. -/
theorem summable_oddThetaTerm_addRight (q U : L) (hU : U ≠ 0) (hq : ‖q‖ < 1) (a : ℤ) :
    Summable (fun n : ℤ => oddThetaTerm q U (n + a)) :=
  (summable_oddThetaTerm q U hU hq).comp_injective (Equiv.addRight a).injective

/-- Summation/reindexing part of the EtTh Proposition 1.4 shift law, assuming
the pointwise term identity supplied by the term-identity work. -/
theorem oddTheta_shift_tsum_of_pointwise (q r U : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0)
    (hU : U ≠ 0) (hq : ‖q‖ < 1) (a : ℤ)
    (hpoint : ∀ n : ℤ,
      oddThetaTerm q (r ^ a * U) n =
        oddThetaSign a * r ^ (-(a ^ 2)) * U ^ (-(2 * a)) *
          oddThetaTerm q U (n + a)) :
    oddTheta q (r ^ a * U) =
      oddThetaSign a * r ^ (-(a ^ 2)) * U ^ (-(2 * a)) * oddTheta q U := by
  rw [oddTheta, oddTheta]
  rw [show (fun n : ℤ => oddThetaTerm q (r ^ a * U) n) =
      (fun n : ℤ => (oddThetaSign a * r ^ (-(a ^ 2)) * U ^ (-(2 * a))) *
        oddThetaTerm q U (n + a)) from funext hpoint]
  rw [tsum_const_mul_addRight_eq]

end LeanFormal.IUT.Foundations.Theta
