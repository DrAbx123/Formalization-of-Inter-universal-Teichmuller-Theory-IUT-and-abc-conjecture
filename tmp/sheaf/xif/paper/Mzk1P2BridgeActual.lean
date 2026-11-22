/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2NormBridgeActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
variable [FiniteDimensional (Padic p) K]
variable [hDVR : IsDiscreteValuationRing (Integers K)]
include localNormedAlgebra
/-- p=2 wrapper: norm against `4 = p^2` is the `2*eK` addVal threshold. -/
theorem p2_norm_le_four_iff_addVal
    (hp2 : p = 2) (π : Integers K) (hπ : Irreducible π) (x : Integers K) :
    ‖(x : K)‖ ≤ ‖((4 : Nat) : K)‖ ↔
      ((2 * logShellRamificationExponent (K := K) (p := p) : Nat) : ℕ∞) ≤ 
        IsDiscreteValuationRing.addVal (Integers K) x := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [IsDiscreteValuationRing.addVal_eq_top_iff]
  · have h4 : ((4 : Nat) : K) = (((p : Nat) ^ 2 : Nat) : K) := by
      rw [hp2]
      norm_num
    rw [h4]
    have h := norm_le_norm_natCast_iff_addVal_ge (K := K) (p := p)
      π hπ x hx 2
    have hfin : IsDiscreteValuationRing.addVal (Integers K) x ≠ ⊤ :=
      (IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr hx
    rw [show ((2 * logShellRamificationExponent (K := K) (p := p) : Nat) : ℕ∞)
        = ((2 : Nat) * logShellRamificationExponent (K := K) (p := p) : ℕ∞) by norm_num]
    rw [← ENat.coe_toNat hfin]
    simpa using h
/-- `logShellScale` at p=2 is 4. -/
theorem logShellScale_two : logShellScale 2 = 4 := by
  simp [logShellScale, logShellScaleExponentFactor]
end LeanFormal.IUT.LocalFieldLogarithm
