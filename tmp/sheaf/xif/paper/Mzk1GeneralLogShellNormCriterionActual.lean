/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2NormBridgeActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import Mathlib.Tactic
/-! # General uniformizer norm/addVal criterion for logShellScale p = p^s -/
noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
variable [FiniteDimensional (Padic p) K]
variable [hDVR : IsDiscreteValuationRing (Integers K)]
include localNormedAlgebra hDVR
/-- General criterion: `‖x‖ ≤ ‖logShellScale p‖` iff `s*eK ≤ addVal x`. -/
theorem norm_le_norm_logShellScale_iff
    (π : Integers K) (hπ : Irreducible π) (x : Integers K) :
    ‖(x : K)‖ ≤ ‖(((logShellScale p : Nat)) : K)‖ ↔
      (((logShellScaleExponentFactor (p := p) *
          logShellRamificationExponent (K := K) (p := p) : Nat) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal (Integers K) x) := by
  by_cases hx : x = 0
  · subst x
    simp [IsDiscreteValuationRing.addVal_zero]
  · have hN := norm_le_norm_natCast_iff_addVal_ge (K := K) (p := p)
      π hπ x hx (logShellScaleExponentFactor (p := p))
    have hscale : ((p : Nat) ^ logShellScaleExponentFactor (p := p) : Nat) =
        logShellScale p := (logShellScale_eq_prime_pow_factor (p := p)).symm
    have hne : IsDiscreteValuationRing.addVal (Integers K) x ≠ ⊤ :=
      IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hx
    have hconv : (((logShellScaleExponentFactor (p := p) *
          logShellRamificationExponent (K := K) (p := p) : Nat) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal (Integers K) x) ↔
      logShellScaleExponentFactor (p := p) *
          logShellRamificationExponent (K := K) (p := p) ≤
        (IsDiscreteValuationRing.addVal (Integers K) x).toNat := by
      rw [← ENat.coe_toNat hne]
      exact ENat.coe_le_coe
    rw [hconv, ← hN]
    congr 1
    rw [hscale]
end LeanFormal.IUT.LocalFieldLogarithm
end