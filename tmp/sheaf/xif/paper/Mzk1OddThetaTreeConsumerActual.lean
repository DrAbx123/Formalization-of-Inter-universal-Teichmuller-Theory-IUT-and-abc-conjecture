import LeanFormal.IUT.Foundations.Theta.OddThetaNonvanishing
import LeanFormal.IUT.Foundations.Theta.OddThetaNormalization

/-!
# Mzk1OddThetaTreeConsumerActual — consumer theorems over the tree odd-theta assets
(OddThetaNonvanishing / OddThetaNormalization, OLEAN_FRESH). Composed projections only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1OddThetaTreeConsumerActual

open LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- Consumer: nonvanishing of the odd theta value at a square root of -1. -/
theorem consumer_oddTheta_ne_zero (q i : L) (hi : i ^ 2 = -1) (hq : ‖q‖ < 1)
    (hq_two : ‖q‖ < ‖(2 : L)‖) : oddTheta q i ≠ 0 :=
  oddTheta_ne_zero_at_i q i hi hq hq_two

/-- Consumer: odd theta quotient transformation law (conditional form). -/
theorem consumer_oddThetaFraction (q r i : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0)
    (hi : i ^ 2 = -1) (hq : ‖q‖ < 1) (hTheta : oddTheta q i ≠ 0) (j : ℤ) :
    oddTheta q (i * r ^ j) / oddTheta q i = r ^ (-(j ^ 2)) :=
  oddThetaFraction_eval q r i hr hr0 hi hq hTheta j

/-- Consumer: odd theta quotient transformation law (unconditional form). -/
theorem consumer_oddThetaFraction_unconditional (q r i : L) (hr : r ^ 2 = q)
    (hr0 : r ≠ 0) (hi : i ^ 2 = -1) (hq : ‖q‖ < 1)
    (hq_two : ‖q‖ < ‖(2 : L)‖) (j : ℤ) :
    oddTheta q (i * r ^ j) / oddTheta q i = r ^ (-(j ^ 2)) :=
  oddThetaFraction_eval_unconditional q r i hr hr0 hi hq hq_two j

/-- Consumer: sign/torsion factor in the shift law at U = i is trivial. -/
theorem consumer_oddThetaSign (i : L) (hi : i ^ 2 = -1) (j : ℤ) :
    oddThetaSign (L := L) j * i ^ (-(2 * j)) = 1 :=
  oddThetaSign_mul_i_zpow_neg_two_mul i hi j

/-- Consumer: odd theta exponent is at least one off {0,-1}. -/
theorem consumer_oddThetaExponent (n : ℤ) (hn : n ∉ ({0, -1} : Finset ℤ)) :
    1 ≤ oddThetaExponent n :=
  oddThetaExponent_one_le_of_not_mem n hn

#check consumer_oddTheta_ne_zero
#check consumer_oddThetaFraction
#check consumer_oddThetaFraction_unconditional
#check consumer_oddThetaSign
#check consumer_oddThetaExponent

end LeanFormal.IUT.XiFPaper.Mzk1OddThetaTreeConsumerActual
end
