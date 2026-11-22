/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Tactic

/-! # P2: actual unit operation preserves integrality (real proof) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2UnitNormActionActual

open LeanFormal.IUT.LocalFieldIntegralUnits

/-- A unit of the local integer ring multiplies the unit ball into itself. -/
theorem p2Unit_mul_mem_unitBall
    {K : Type*} [NormedField K] [IsUltrametricDist K]
    (u : (Integers K)ˣ) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖((u.val : K) * x)‖ ≤ 1 := by
  rw [norm_mul, norm_unit_eq_one u, one_mul]
  exact hx

/-- The same for membership in the actual integer ring. -/
theorem p2Unit_mul_mem_integers
    {K : Type*} [NormedField K] [IsUltrametricDist K]
    (u : (Integers K)ˣ) {x : K} (hx : x ∈ Integers K) :
    (u.val : K) * x ∈ Integers K := by
  rw [mem_integers_iff] at hx ⊢
  rw [norm_mul, norm_unit_eq_one u]
  simpa using hx

end LeanFormal.IUT.XiFPaper.Mzk1P2UnitNormActionActual

end