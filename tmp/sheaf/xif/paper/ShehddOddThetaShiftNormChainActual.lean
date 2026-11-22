import LeanFormal.IUT.Foundations.Theta.OddThetaShift
import LeanFormal.IUT.Foundations.Theta.OddThetaNormalization

/-!
# ShehddOddThetaShiftNormChainActual — odd theta shift/fraction norm chain

New chain consequences of the compiled odd theta shift and normalized fraction laws: the
norm-level shift law (sign factor has norm one) and the log-level normalized evaluation.
No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddOddThetaShiftNormChainActual

open LeanFormal.IUT
open LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- **PROVED chain:** the shift law at the norm level, using that the sign factor has
norm one. -/
theorem oddTheta_shift_norm_chain (q r U : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0)
    (hU : U ≠ 0) (hq : ‖q‖ < 1) (a : Int) :
    ‖oddTheta q (r ^ a * U)‖ =
      ‖r‖ ^ (-(a ^ 2)) * ‖U‖ ^ (-(2 * a)) * ‖oddTheta q U‖ := by
  rw [oddTheta_shift q r U hr hr0 hU hq a, norm_mul, norm_mul, norm_mul,
    norm_oddThetaSign, one_mul]
  simp only [norm_zpow]

/-- **PROVED chain:** the normalized theta fraction evaluation at U = i r^j, made
unconditional by the compiled nonvanishing at i. -/
theorem oddTheta_fraction_norm_chain (q r i : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0)
    (hi : i ^ 2 = -1) (hq : ‖q‖ < 1) (hq_two : ‖q‖ < ‖(2 : L)‖) (j : Int) :
    oddTheta q (i * r ^ j) / oddTheta q i = r ^ (-(j ^ 2)) :=
  oddThetaFraction_eval_unconditional q r i hr hr0 hi hq hq_two j

/-- **PROVED chain:** the same evaluation at the norm level. -/
theorem oddTheta_fraction_norm_value_chain (q r i : L) (hr : r ^ 2 = q)
    (hr0 : r ≠ 0) (hi : i ^ 2 = -1) (hq : ‖q‖ < 1)
    (hq_two : ‖q‖ < ‖(2 : L)‖) (j : Int) :
    ‖oddTheta q (i * r ^ j) / oddTheta q i‖ = ‖r‖ ^ (-(j ^ 2)) := by
  rw [oddTheta_fraction_norm_chain q r i hr hr0 hi hq hq_two j, norm_zpow]

end LeanFormal.IUT.XiFPaper.ShehddOddThetaShiftNormChainActual
end
