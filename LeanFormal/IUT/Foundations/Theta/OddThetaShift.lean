import LeanFormal.IUT.Foundations.Theta.OddThetaTermAlgebra
import LeanFormal.IUT.Foundations.Theta.OddThetaShiftSum

set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.IUT.Foundations.Theta

universe u
variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- EtTh Proposition 1.4 (ii): the actual shift law of the odd theta series. -/
theorem oddTheta_shift (q r U : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0)
    (hU : U ≠ 0) (hq : ‖q‖ < 1) (a : ℤ) :
    oddTheta q (r ^ a * U) =
      oddThetaSign a * r ^ (-(a ^ 2)) * U ^ (-(2 * a)) * oddTheta q U := by
  refine oddTheta_shift_tsum_of_pointwise q r U hr hr0 hU hq a ?_
  intro n
  simpa [oddThetaShiftCoefficient] using oddThetaTerm_shift q r U hr hr0 hU a n

end LeanFormal.IUT.Foundations.Theta
