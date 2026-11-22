/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateQSeriesEval
import Mathlib.Tactic
/-! # Tate H decomposition -/
noncomputable section
namespace LeanFormal.IUT.PAdicAnalytic.Node09TateHSpecialValue
open LeanFormal.IUT.PAdicAnalytic
open PowerSeries

local instance fivePrimeFactTateH : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
/-- H has the form X + X^2 G. -/
theorem tateHFormal_eq_X_add_sq_mul :
    ∃ G : PowerSeries (PadicInt 5), tateHFormal = X + X ^ 2 * G := by
  obtain ⟨G, hG⟩ := tateHFormal_sub_X_dvd_X_sq
  exact ⟨G, by
    rw [← hG]
    ring_nf⟩
/-- Consequently the evaluation of H at any q is q + q^2 * eval G q. -/
theorem padicPowerSeriesEval_tateHFormal_eq_X_add_sq_mul
    {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    ∃ G : PowerSeries (PadicInt 5),
      padicPowerSeriesEval tateHFormal q =
        q + q ^ 2 * padicPowerSeriesEval G q := by
  obtain ⟨G, hG⟩ := tateHFormal_eq_X_add_sq_mul
  refine ⟨G, ?_⟩
  rw [hG, padicPowerSeriesEval_add _ _ hq,
    padicPowerSeriesEval_mul _ _ hq, padicPowerSeriesEval_pow _ 2 hq,
    padicPowerSeriesEval_X]
end LeanFormal.IUT.PAdicAnalytic.Node09TateHSpecialValue
end