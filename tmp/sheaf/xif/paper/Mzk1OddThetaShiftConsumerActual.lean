import LeanFormal.IUT.Foundations.Theta.OddThetaShift
import LeanFormal.IUT.Foundations.Theta.OddThetaShiftSum
import LeanFormal.IUT.Foundations.Theta.OddThetaNegativeDecay

/-!
# Mzk1OddThetaShiftConsumerActual — consumer theorems over the odd-theta shift/summation/
negative-decay assets (OLEAN_FRESH). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1OddThetaShiftConsumerActual

open LeanFormal.IUT.Foundations.Theta
open scoped BigOperators

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- Consumer: odd theta shift law (r^2=q, r≠0, U≠0, ‖q‖<1). -/
theorem consumer_oddTheta_shift (q r U : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0)
    (hU : U ≠ 0) (hq : ‖q‖ < 1) (a : ℤ) :
    oddTheta q (r ^ a * U) = oddTheta q U :=
  oddTheta_shift q r U hr hr0 hU hq a

/-- Consumer: tsum is invariant under add-right. -/
theorem consumer_tsum_addRight (f : ℤ → L) (a : ℤ) :
    (∑' n : ℤ, f (n + a)) = ∑' n : ℤ, f n :=
  tsum_addRight_eq_tsum f a

/-- Consumer: the shifted odd theta term is summable. -/
theorem consumer_summable_shift (q U : L) (hU : U ≠ 0) (hq : ‖q‖ < 1) (a : ℤ) :
    Summable (fun n : ℤ => oddThetaTerm q U (n + a)) :=
  summable_oddThetaTerm_addRight q U hU hq a

/-- Consumer: odd theta exponent is invariant under neg-succ. -/
theorem consumer_oddThetaExponent_neg_succ (n : ℕ) :
    oddThetaExponent (-((n : ℤ) + 1)) = oddThetaExponent (n : ℤ) :=
  oddThetaExponent_neg_succ n

/-- Consumer: odd theta term relation under neg-succ. -/
theorem consumer_oddThetaTerm_neg_succ (q U : L) (n : ℕ) :
    oddThetaTerm q U (-((n : ℤ) + 1)) = - oddThetaTerm q U⁻¹ (n : ℤ) :=
  oddThetaTerm_neg_succ q U n

#check consumer_oddTheta_shift
#check consumer_tsum_addRight
#check consumer_summable_shift
#check consumer_oddThetaExponent_neg_succ
#check consumer_oddThetaTerm_neg_succ

end LeanFormal.IUT.XiFPaper.Mzk1OddThetaShiftConsumerActual
end
