/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
/-- The congruence-quotient cardinal follows from the unit-group identification
and the truncated unit-group count. -/
theorem card_logShellCongruenceQuotient_of_unitsEquiv
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    {p : Nat} [Fact p.Prime] [NormedAlgebra (Padic p) K]
    (e : Nat)
    (eEquiv : ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) ≃*
      (Integers K ⧸ Ideal.span
        {(((logShellScale p : ℕ) ^ e : ℕ) : Integers K)})ˣ)
    (hcard : Nat.card ((Integers K ⧸ Ideal.span
        {(((logShellScale p : ℕ) ^ e : ℕ) : Integers K)})ˣ) =
      (logShellResidueCard (K := K) - 1) *
        logShellResidueCard (K := K) ^
          (e * logShellScaleExponentFactor (p := p) - 1)) :
    Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      (logShellResidueCard (K := K) - 1) *
        logShellResidueCard (K := K) ^
          (e * logShellScaleExponentFactor (p := p) - 1) :=
  (Nat.card_congr eEquiv.toEquiv).trans hcard

end LeanFormal.IUT.LocalFieldLogarithm
