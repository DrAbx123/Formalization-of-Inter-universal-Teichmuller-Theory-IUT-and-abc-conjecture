/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-! # q-pilot: consumers combining log-volume and base-change identities -/

namespace LeanFormal.IUT

open NumberFieldFinitePlace ArithmeticQPilotLogVolume ArithmeticQPilotBaseChange

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}

/-- The completed q-candidate lies in (0,1). -/
theorem qNorm_mem_Ioo (parameter : FinitePlaceQCandidate place) :
    0 < ‖parameter.q‖ ∧ ‖parameter.q‖ < 1 := 
  ⟨qNorm_pos parameter, qNorm_lt_one parameter⟩

/-- The completion norm is recovered from the exponent and the residue-norm base. -/
theorem exp_neg_exponent_mul_residueLog_eq_qNorm
    (parameter : FinitePlaceQCandidate place) :
    Real.exp (-((parameter.exponent : ℝ) * Real.log (residueNormBase place))) =
      ‖parameter.q‖ := by
  rw [← localLogMagnitude_eq_exponent_mul_log parameter]
  exact exp_neg_localLogMagnitude parameter

/-- Positivity of the order times the residue logarithm (the local volume denominator). -/
theorem order_mul_residueLog_pos (parameter : FinitePlaceQCandidate place) :
    0 < (parameter.order : ℝ) * Real.log (residueNormBase place) := by
  rw [← localLogMagnitude_eq_order_mul_log parameter]
  exact localLogMagnitude_pos parameter

/-- The signed local logarithm is the negative of the order times the residue logarithm. -/
theorem localSignedLog_eq_neg_order_mul_residueLog
    (parameter : FinitePlaceQCandidate place) :
    localSignedLog parameter =
      -((parameter.order : ℝ) * Real.log (residueNormBase place)) := by
  rw [localSignedLog_eq_neg_magnitude, localLogMagnitude_eq_order_mul_log]

end

end LeanFormal.IUT
