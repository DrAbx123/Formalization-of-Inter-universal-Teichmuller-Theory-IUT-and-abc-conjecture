/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TruncatedUnitsCountActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.IUTIV.Estimates.DifferentDegreeUpperBound
import Mathlib.Tactic
/-! # Primary truncated units card: span `(p^s) = m^(eK*s)` and unconditional count -/
noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.IUTIV.Estimates
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
variable [FiniteDimensional (Padic p) K]
include localNormedAlgebra
/-- The ideal `(p^s) = (logShellScale p)` is the `eK*s`-th power of the maximal ideal. -/
theorem span_logShellScale_eq_maximalIdeal_pow :
    Ideal.span {((logShellScale p : Nat) : Integers K)} =
      (IsLocalRing.maximalIdeal (Integers K)) ^
        (logShellRamificationExponent (K := K) (p := p) *
          logShellScaleExponentFactor (p := p)) := by
  letI : IsDiscreteValuationRing (Integers K) :=
    integersIsDiscreteValuationRing (p := p) (L := K)
  letI : IsDedekindDomain (Integers K) := integersIsDedekindDomain (p := p) (L := K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Integers K)
  obtain ⟨n, u, hp_eq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (prime_ne_zero_integers (K := K) (p := p)) hϖ
  have hadd : IsDiscreteValuationRing.addVal (Integers K) ((p : Integers K)) =
      (n : ℕ∞) := by
    rw [hp_eq]
    exact IsDiscreteValuationRing.addVal_def' u hϖ n
  have hn : logShellRamificationExponent (K := K) (p := p) = n := by
    have hram := addVal_prime_eq_ramificationExponent (K := K) (p := p)
    have hval : ramifiedPrimeAddVal (K := K) (p := p) = (n : ℕ∞) := by
      simpa [ramifiedPrimeAddVal] using hadd
    have := congrArg ENat.toNat (hram.symm.trans hval)
    simpa [logShellRamificationExponent] using this
  have hscale : ((logShellScale p : Nat) : Integers K) =
      ((p : Integers K)) ^ logShellScaleExponentFactor (p := p) := by
    rw [logShellScale_eq_prime_pow_factor]
    push_cast
    rfl
  have hspan1 : Ideal.span {(p : Integers K)} = (Ideal.span {ϖ}) ^ n := by
    rw [hp_eq, Ideal.span_singleton_mul_left_unit u.isUnit, Ideal.span_singleton_pow]
  calc Ideal.span {((logShellScale p : Nat) : Integers K)}
      = (Ideal.span {(p : Integers K)}) ^ logShellScaleExponentFactor (p := p) := by
          rw [hscale, Ideal.span_singleton_pow]
    _ = ((Ideal.span {ϖ}) ^ n) ^ logShellScaleExponentFactor (p := p) := by
          rw [hspan1]
    _ = (Ideal.span {ϖ}) ^ (n * logShellScaleExponentFactor (p := p)) := by
          rw [pow_mul]
    _ = (IsLocalRing.maximalIdeal (Integers K)) ^
          (n * logShellScaleExponentFactor (p := p)) := by
          rw [← hϖ.maximalIdeal_eq]
    _ = (IsLocalRing.maximalIdeal (Integers K)) ^
          (logShellRamificationExponent (K := K) (p := p) *
            logShellScaleExponentFactor (p := p)) := by
          rw [hn]
/-- Unconditional primary truncated-units cardinal. -/
theorem truncatedUnitsCardPrimary :
    TruncatedUnitsCardPrimary (K := K) (p := p) := by
  apply truncatedUnitsCardPrimary_of_span_eq (K := K) (p := p)
  · exact Nat.succ_le_of_lt (Nat.mul_pos
      (logShellRamificationExponent_pos (K := K) (p := p))
      (logShellScaleExponentFactor_pos (p := p)))
  · exact span_logShellScale_eq_maximalIdeal_pow (K := K) (p := p)
end LeanFormal.IUT.LocalFieldLogarithm
end