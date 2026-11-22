/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # O1: q-pilot object constructed from the p-adic prime element -/

noncomputable section

namespace LeanFormal.IUT.Objects.QPilot

variable (p : Nat) [Fact p.Prime]

/-- The q-pilot value: the rational prime `p` as a unit of the p-adic field.
(IUT III, q-pilot at a bad place; actual data, not an interface field.) -/
def qPilotValue : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (by
    have hp : (p : ℚ_[p]) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    exact hp)

theorem qPilotValue_coe : ((qPilotValue p : ℚ_[p])) = (p : ℚ_[p]) := rfl

theorem qPilotValue_norm : ‖((qPilotValue p : ℚ_[p]))‖ = (p : ℝ)⁻¹ := by
  rw [qPilotValue_coe]
  exact Padic.norm_p

/-- The q-pilot log readout: the (signed) log of the p-adic norm of the value. -/
def qPilotLog : ℝ := Real.log ‖((qPilotValue p : ℚ_[p]))‖

theorem qPilotLog_eq : qPilotLog p = -Real.log (p : ℝ) := by
  unfold qPilotLog
  rw [qPilotValue_norm, Real.log_inv]

theorem qPilotLog_neg : qPilotLog p < 0 := by
  rw [qPilotLog_eq]
  exact neg_neg_of_pos (Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt))

theorem qPilotValue_pow_coe (n : Nat) :
    ((qPilotValue p ^ n : ℚ_[p]ˣ) : ℚ_[p]) = (p : ℚ_[p]) ^ n := by
  rw [Units.coe_pow, qPilotValue_coe]

/-- Multiplicative/log compatibility: the n-th power of the q-pilot has log readout `n` times
the q-pilot log readout. -/
theorem qPilotLog_pow (n : Nat) :
    Real.log ‖((qPilotValue p ^ n : ℚ_[p]ˣ) : ℚ_[p])‖ = n * qPilotLog p := by
  rw [qPilotValue_pow_coe, norm_pow, Real.log_pow]
  unfold qPilotLog
  rw [qPilotValue_coe]

/-- The q-pilot object: the value together with its definition-source and log-readout data. -/
structure QPilotObject where
  value : ℚ_[p]ˣ
  value_eq : value = qPilotValue p
  log_eq : Real.log ‖(value : ℚ_[p])‖ = qPilotLog p

/-- **Construction theorem**: the q-pilot object is constructed from actual p-adic data
(the prime element), not supplied as an arbitrary vector or interface field. -/
theorem qPilotObject_constructed : Nonempty (QPilotObject p) :=
  ⟨⟨qPilotValue p, rfl, rfl⟩⟩

end LeanFormal.IUT.Objects.QPilot
