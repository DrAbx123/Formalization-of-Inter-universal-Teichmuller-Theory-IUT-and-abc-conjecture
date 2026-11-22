/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TruncatedUnitsPrimaryActual
import Mathlib.Tactic
/-! # Secondary (general-e) truncated units card -/
noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
variable [FiniteDimensional (Padic p) K]
include localNormedAlgebra
/-- The e-th power ideal is the `eK*s*e`-th power of the maximal ideal. -/
theorem span_logShellScale_pow_eq_maximalIdeal_pow (e : Nat) :
    Ideal.span {(((logShellScale p : Nat) ^ e : Nat) : Integers K)} =
      (IsLocalRing.maximalIdeal (Integers K)) ^
        (logShellRamificationExponent (K := K) (p := p) *
          logShellScaleExponentFactor (p := p) * e) := by
  calc Ideal.span {(((logShellScale p : Nat) ^ e : Nat) : Integers K)}
      = (Ideal.span {((logShellScale p : Nat) : Integers K)}) ^ e := by
          have hcast : (((logShellScale p : Nat) ^ e : Nat) : Integers K) =
              ((logShellScale p : Nat) : Integers K) ^ e := by
            push_cast
            rfl
          rw [hcast, Ideal.span_singleton_pow]
    _ = ((IsLocalRing.maximalIdeal (Integers K)) ^
          (logShellRamificationExponent (K := K) (p := p) *
            logShellScaleExponentFactor (p := p))) ^ e := by
          rw [span_logShellScale_eq_maximalIdeal_pow (K := K) (p := p)]
    _ = (IsLocalRing.maximalIdeal (Integers K)) ^
          (logShellRamificationExponent (K := K) (p := p) *
            logShellScaleExponentFactor (p := p) * e) := by
          rw [← pow_mul]
/-- Secondary truncated-units cardinal, `e >= 1`. -/
theorem truncatedUnitsCardCorrected (e : Nat) (he : 1 ≤ e) :
    TruncatedUnitsCardCorrected (K := K) (p := p) e := by
  unfold TruncatedUnitsCardCorrected
  rw [span_logShellScale_pow_eq_maximalIdeal_pow (K := K) (p := p) e]
  exact card_units_quotient_maximalIdeal_pow (K := K) (p := p)
    (logShellRamificationExponent (K := K) (p := p) *
      logShellScaleExponentFactor (p := p) * e)
    (Nat.succ_le_of_lt (Nat.mul_pos
      (Nat.mul_pos (logShellRamificationExponent_pos (K := K) (p := p))
        (logShellScaleExponentFactor_pos (p := p)))
      (lt_of_lt_of_le Nat.zero_lt_one he)))
end LeanFormal.IUT.LocalFieldLogarithm
end