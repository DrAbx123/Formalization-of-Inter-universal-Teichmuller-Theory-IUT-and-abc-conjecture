import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.NumberFieldFinitePlace.OrderAudit

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}

/-- The FinitePlaceQCandidate order is the positive additive valuation
height of the local q parameter, not a group-theoretic order. -/
theorem order_eq_valuation_height
    (parameter : FinitePlaceQCandidate place) :
    (parameter.order : ℤ) =
      -Multiplicative.toAdd
        (WithZero.unzero parameter.valuation_ne_zero) := by
  unfold FinitePlaceQCandidate.order FinitePlaceQCandidate.exponent
  exact Int.toNat_of_nonneg (le_of_lt parameter.exponent_pos)

/-- The same order as a natural valuation height. -/
theorem order_eq_nat_valuation_height
    (parameter : FinitePlaceQCandidate place) :
    parameter.order =
      Int.toNat (-Multiplicative.toAdd
        (WithZero.unzero parameter.valuation_ne_zero)) := by
  rfl

end LeanFormal.IUT.NumberFieldFinitePlace.OrderAudit

end
