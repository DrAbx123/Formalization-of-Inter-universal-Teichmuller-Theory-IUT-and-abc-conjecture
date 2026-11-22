/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmCongruenceEquiv
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import LeanFormal.IUT.IUTIV.Estimates.DifferentDegreeUpperBound
import Mathlib.Tactic
/-! # Task 126-127: corrected truncated-units pairing and cardinal target

`logShellScale p = p^s`; the target ideal `(logShellScale p)^e = (p^s)^e`
has m-adic exponent `e_K * s * e`, where `e_K = logShellRamificationExponent K p`.
The old exponent `e*s-1` is only the `e_K = 1` specialization.

For the congruence units: `logShellCongruenceUnits` uses closed radius
`‖logShellScale p‖`, i.e. the ideal `p^s O`, NOT `(p^s)^e O`.  Hence the
existing radius and the e-th power target ideal only pair at `e = 1`;
`logShellCongruenceUnitsPow e` below uses radius `‖(p^s)^e‖` and is the
correct kernel for the e-th power quotient. -/
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
/-- Corrected target for the units of `O ⧸ (logShellScale p)^e`:
m-adic exponent `eK * s * e`. -/
def TruncatedUnitsCardCorrected (e : Nat) : Prop :=
  Nat.card ((Integers K ⧸ Ideal.span
    {(((logShellScale p : Nat) ^ e : Nat) : Integers K)})ˣ) =
      (logShellResidueCard (K := K) - 1) *
        logShellResidueCard (K := K) ^
          (logShellRamificationExponent (K := K) (p := p) *
            logShellScaleExponentFactor (p := p) * e - 1)
/-- **Primary target** for the actual congruence quotient: units of `O/(p^s)`. -/
def TruncatedUnitsCardPrimary : Prop :=
  Nat.card ((Integers K ⧸ Ideal.span
    {((logShellScale p : Nat) : Integers K)})ˣ) =
      (logShellResidueCard (K := K) - 1) *
        logShellResidueCard (K := K) ^
          (logShellRamificationExponent (K := K) (p := p) *
            logShellScaleExponentFactor (p := p) - 1)
/-- Definitional form of the primary target. -/
theorem truncatedUnitsCardPrimary_card_iff :
    TruncatedUnitsCardPrimary (K := K) (p := p) ↔
      Nat.card ((Integers K ⧸ Ideal.span
        {((logShellScale p : Nat) : Integers K)})ˣ) =
          (logShellResidueCard (K := K) - 1) *
            logShellResidueCard (K := K) ^
              (logShellRamificationExponent (K := K) (p := p) *
                logShellScaleExponentFactor (p := p) - 1) := Iff.rfl
/-- Unramified specialization: `e_K = 1` recovers the old exponent. -/
theorem truncatedUnitsCardCorrected_of_ramificationExponent_one
    (he : logShellRamificationExponent (K := K) (p := p) = 1) :
    TruncatedUnitsCardCorrected (K := K) (p := p) e ↔
      Nat.card ((Integers K ⧸ Ideal.span
        {(((logShellScale p : Nat) ^ e : Nat) : Integers K)})ˣ) =
          (logShellResidueCard (K := K) - 1) *
            logShellResidueCard (K := K) ^
              (logShellScaleExponentFactor (p := p) * e - 1) := by
  unfold TruncatedUnitsCardCorrected
  rw [he]
  simp only [Nat.one_mul]

/-- Congruence units at the e-th power radius: kernel for `(p^s)^e O`. -/
def logShellCongruenceUnitsPow (e : Nat) : Subgroup (Integers K)ˣ :=
  principalUnitsAtClosedRadius
    ‖(((logShellScale p : Nat) ^ e : Nat) : K)‖
    (norm_nonneg _)
/-- Exact radius/power pairing assertion: at `e = 1` the power-radius subgroup
is the existing `logShellCongruenceUnits`. -/
theorem logShellCongruenceUnitsPow_one :
    logShellCongruenceUnitsPow (K := K) (p := p) 1 =
      logShellCongruenceUnits (K := K) (p := p) := by
  unfold logShellCongruenceUnitsPow logShellCongruenceUnits
  simp
/-- Quotient size of maximal-ideal powers, using the existing Dedekind instances. -/
theorem cardQuot_maximalIdeal_pow (N : Nat) :
    Submodule.cardQuot ((IsLocalRing.maximalIdeal (Integers K)) ^ N) =
      Submodule.cardQuot (IsLocalRing.maximalIdeal (Integers K)) ^ N := by
  letI : IsDiscreteValuationRing (Integers K) := integersIsDiscreteValuationRing (p := p)
  letI : IsDedekindDomain (Integers K) := integersIsDedekindDomain (p := p)
  exact cardQuot_pow_of_prime (dvr_maximalIdeal_ne_bot (Integers K))
end LeanFormal.IUT.LocalFieldLogarithm
end