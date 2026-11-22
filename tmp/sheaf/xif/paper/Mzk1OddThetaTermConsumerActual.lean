import LeanFormal.IUT.Foundations.Theta.OddThetaTermAlgebra
import LeanFormal.IUT.Foundations.Theta.OddThetaShift

/-!
# Mzk1OddThetaTermConsumerActual — consumer theorems over the odd theta term algebra
(tree assets, OLEAN_FRESH). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1OddThetaTermConsumerActual

open LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- Consumer: the odd theta sign is a square root of unity. -/
theorem consumer_oddThetaSign_sq (a : ℤ) :
    oddThetaSign (L := L) a * oddThetaSign a = 1 :=
  oddThetaSign_sq a

/-- Consumer: shift formula for doubled odd theta exponents. -/
theorem consumer_two_mul_oddThetaExponent_add (n a : ℤ) :
    2 * (oddThetaExponent (n + a) : ℤ) =
      2 * (oddThetaExponent n : ℤ) + a * (2 * n + a + 1) :=
  two_mul_oddThetaExponent_add n a

/-- Consumer: odd theta term shift law. -/
theorem consumer_oddThetaTerm_shift (q r U : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0)
    (hU : U ≠ 0) (a n : ℤ) :
    oddThetaTerm q (r ^ a * U) n =
      oddThetaShiftCoefficient r U a * oddThetaTerm q U (n + a) :=
  oddThetaTerm_shift q r U hr hr0 hU a n

/-- Consumer: inverse form of the odd theta term shift law. -/
theorem consumer_oddThetaTerm_shift_inv (q r U : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0)
    (hU : U ≠ 0) (a n : ℤ) :
    oddThetaTerm q U (n + a) =
      (oddThetaShiftCoefficient r U a)⁻¹ * oddThetaTerm q (r ^ a * U) n :=
  oddThetaTerm_shift_inv q r U hr hr0 hU a n

#check consumer_oddThetaSign_sq
#check consumer_two_mul_oddThetaExponent_add
#check consumer_oddThetaTerm_shift
#check consumer_oddThetaTerm_shift_inv

end LeanFormal.IUT.XiFPaper.Mzk1OddThetaTermConsumerActual
end
