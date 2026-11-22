/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1IutIVProp14TorsionFromUnitsActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
def MissingCongruenceUnitsEquiv
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    {p : Nat} [Fact p.Prime] [NormedAlgebra (Padic p) K] (e : Nat) : Prop :=
  Nonempty (((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) ≃*
    (Integers K ⧸ Ideal.span
      {(((logShellScale p : ℕ) ^ e : ℕ) : Integers K)})ˣ)
def MissingTruncatedUnitsCard
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    {p : Nat} [Fact p.Prime] [NormedAlgebra (Padic p) K]
    (e s : Nat) : Prop :=
  Nat.card ((Integers K ⧸ Ideal.span
      {(((logShellScale p : ℕ) ^ e : ℕ) : Integers K)})ˣ) =
    (logShellResidueCard (K := K) - 1) *
      logShellResidueCard (K := K) ^ (e * s - 1)
theorem torsion_card_eq_actual_of_missing
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    {p : Nat} [Fact p.Prime] [NormedAlgebra (Padic p) K]
    {e f s : Nat}
    (he : MissingCongruenceUnitsEquiv (K := K) (p := p) e)
    (hc : MissingTruncatedUnitsCard (K := K) (p := p) e s)
    (hs : logShellScaleExponentFactor (p := p) = s)
    (hq : logShellResidueCard (K := K) = p ^ f)
    (hcop : Nat.Coprime p (logShellResidueCard (K := K) - 1)) :
    ∃ h m : Nat,
      Nat.card (LogShellIntegerQuotient (K := K) (p := p)) = p ^ h ∧
      Nat.card (CommGroup.torsion (Integers K)ˣ) =
        (logShellResidueCard (K := K) - 1) * p ^ m ∧
      h + m = f * (e * s - 1) := by
  obtain ⟨eEquiv⟩ := he
  exact torsion_card_eq_actual_of_unitsEquiv eEquiv hc hs hq hcop
end LeanFormal.IUT.LocalFieldLogarithm
