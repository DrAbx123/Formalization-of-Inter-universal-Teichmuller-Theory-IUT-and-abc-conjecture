/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-! # q-pilot: derived normalization identities (consumer of base-change and log-volume) -/

namespace LeanFormal.IUT

namespace ArithmeticQPilotBaseChange

open NumberFieldFinitePlace ArithmeticQPilotLogVolume

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}

theorem orderNormalizedMagnitude_eq_exponent
    (parameter : FinitePlaceQCandidate place) :
    orderNormalizedMagnitude parameter = (parameter.exponent : ℝ) := by
  rw [orderNormalizedMagnitude_eq_order, qOrder_cast_eq_exponent_cast]

theorem orderNormalizedMagnitude_ne_zero
    (parameter : FinitePlaceQCandidate place) :
    orderNormalizedMagnitude parameter ≠ 0 := by
  rw [orderNormalizedMagnitude_eq_exponent]
  exact_mod_cast ne_of_gt parameter.exponent_pos

theorem localLogMagnitude_eq_exponent_mul_residueLog
    (parameter : FinitePlaceQCandidate place) :
    localLogMagnitude parameter =
      (parameter.exponent : ℝ) * Real.log (residueNormBase place) := 
  localLogMagnitude_eq_exponent_mul_log parameter

theorem orderNormalizedMagnitude_eq_iff_exponent_eq
    (p q : FinitePlaceQCandidate place) :
    orderNormalizedMagnitude p = orderNormalizedMagnitude q ↔ p.exponent = q.exponent := by
  rw [orderNormalizedMagnitude_eq_exponent, orderNormalizedMagnitude_eq_exponent]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

end

end ArithmeticQPilotBaseChange

end LeanFormal.IUT
