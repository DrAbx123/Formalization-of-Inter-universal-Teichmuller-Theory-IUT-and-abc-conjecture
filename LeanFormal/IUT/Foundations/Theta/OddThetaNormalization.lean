import LeanFormal.IUT.Foundations.Theta.OddThetaShift
import LeanFormal.IUT.Foundations.Theta.OddThetaNonvanishing

set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.IUT.Foundations.Theta

universe u
variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- The sign/torsion factor in the shift law at U = i is trivial. -/
theorem oddThetaSign_mul_i_zpow_neg_two_mul (i : L) (hi : i ^ 2 = -1) (j : ℤ) :
    oddThetaSign (L := L) j * i ^ (-(2 * j)) = 1 := by
  have h2 : i ^ (-(2 * j)) = (-1 : L) ^ (-j) := by
    have hexp : -(2 * j) = (2 : ℤ) * (-j) := by ring
    rw [hexp]
    calc i ^ ((2 : ℤ) * (-j)) = (i ^ (2 : ℤ)) ^ (-j) :=
          zpow_mul i (2 : ℤ) (-j)
      _ = (-1 : L) ^ (-j) := by
        rw [show i ^ (2 : ℤ) = -1 from (zpow_natCast i 2).trans hi]
  rw [oddThetaSign_eq_pow j, h2, ← zpow_add₀ (by norm_num : (-1 : L) ≠ 0)]
  rw [show j + -j = 0 by ring]
  norm_num

/-- The quotient theta function f(U) = Theta(q,U)/Theta(q,i), conditional on
nonvanishing at i. -/
theorem oddThetaFraction_eval (q r i : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0)
    (hi : i ^ 2 = -1) (hq : ‖q‖ < 1) (hTheta : oddTheta q i ≠ 0) (j : ℤ) :
    oddTheta q (i * r ^ j) / oddTheta q i = r ^ (-(j ^ 2)) := by
  have hi0 : i ≠ 0 := by
    intro h
    rw [h] at hi
    norm_num at hi
  rw [mul_comm i (r ^ j), oddTheta_shift q r i hr hr0 hi0 hq j]
  rw [show oddThetaSign (L := L) j * r ^ (-(j ^ 2)) * i ^ (-(2 * j)) *
        oddTheta q i
      = (oddThetaSign (L := L) j * i ^ (-(2 * j))) * r ^ (-(j ^ 2)) *
        oddTheta q i by ring]
  rw [oddThetaSign_mul_i_zpow_neg_two_mul i hi j, one_mul]
  exact mul_div_cancel_right₀ _ hTheta

/-- Unconditional normalized theta evaluation at U = i r^j. -/
theorem oddThetaFraction_eval_unconditional (q r i : L) (hr : r ^ 2 = q)
    (hr0 : r ≠ 0) (hi : i ^ 2 = -1) (hq : ‖q‖ < 1)
    (hq_two : ‖q‖ < ‖(2 : L)‖) (j : ℤ) :
    oddTheta q (i * r ^ j) / oddTheta q i = r ^ (-(j ^ 2)) :=
  oddThetaFraction_eval q r i hr hr0 hi hq
    (oddTheta_ne_zero_at_i q i hi hq hq_two) j

end LeanFormal.IUT.Foundations.Theta
