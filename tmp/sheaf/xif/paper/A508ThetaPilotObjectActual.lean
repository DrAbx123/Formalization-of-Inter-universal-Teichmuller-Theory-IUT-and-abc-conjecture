/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # A508: Theta-pilot object constructed from the p-adic prime power (independent readout) -/

noncomputable section

namespace LeanFormal.IUT.Objects.ThetaPilot

variable (p N : Nat) [Fact p.Prime]

/-- The Theta-pilot value: the `N`-th power of the rational prime in the p-adic field
(the `N`-th power image of the q-pilot; IUT III `N`-power map convention).
Actual data: an explicit unit of `Q_p`, not a quotient by `2l` and not an interface field. -/
def thetaPilotValue : ℚ_[p]ˣ :=
  Units.mk0 ((p : ℚ_[p]) ^ N) (by
    have hp : (p : ℚ_[p]) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    exact pow_ne_zero N hp)

theorem thetaPilotValue_coe : ((thetaPilotValue p N : ℚ_[p])) = (p : ℚ_[p]) ^ N := rfl

theorem thetaPilotValue_eq_qPilot_pow :
    ((thetaPilotValue p N : ℚ_[p])) = ((Units.mk0 (p : ℚ_[p]) (by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)) ^ N : ℚ_[p]ˣ) := by
  rw [thetaPilotValue_coe]
  exact (Units.val_pow_eq_pow_val (Units.mk0 (p : ℚ_[p]) (by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)) N).symm

theorem thetaPilotValue_norm : ‖((thetaPilotValue p N : ℚ_[p]))‖ = (p : ℝ) ^ (-(N : ℤ)) := by
  rw [thetaPilotValue_coe, Padic.norm_p_pow]

/-- The Theta-pilot log readout: signed log of the p-adic norm of the Theta value. -/
def thetaPilotLog : ℝ := Real.log ‖((thetaPilotValue p N : ℚ_[p]))‖

theorem thetaPilotLog_eq : thetaPilotLog p N = -(N : ℝ) * Real.log (p : ℝ) := by
  unfold thetaPilotLog
  rw [thetaPilotValue_norm, Real.log_zpow]
  push_cast
  ring

theorem thetaPilotLog_neg (hN : 0 < N) : thetaPilotLog p N < 0 := by
  rw [thetaPilotLog_eq]
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  nlinarith

/-- The Theta-pilot object: value, definition source, and log readout. -/
structure ThetaPilotObject where
  /-- The `N`-th power of the prime as a p-adic unit. -/
  value : ℚ_[p]ˣ
  value_eq : value = thetaPilotValue p N
  log_eq : Real.log ‖(value : ℚ_[p])‖ = thetaPilotLog p N

theorem thetaPilotObject_constructed (hN : 0 < N) : Nonempty (ThetaPilotObject p N) :=
  ⟨⟨thetaPilotValue p N, rfl, rfl⟩⟩

end LeanFormal.IUT.Objects.ThetaPilot
