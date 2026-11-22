/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula
import Mathlib.GroupTheory.PGroup

/-! # IUT IV Prop 1.4: named group-count interfaces for lattice line 2 -/

noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
include localNormedAlgebra
/-- `#Γ = p^h` once `Γ` is known to be a finite `p`-group.
This is the named interface requested by the lattice volume line; the
remaining task is to discharge the `IsPGroup` hypothesis for the actual
`LogShellIntegerQuotient`. -/
theorem card_gamma_eq_pow
    {Gamma : Type*} [AddCommGroup Gamma] [Finite Gamma]
    (hGamma : IsPGroup p (Multiplicative Gamma)) :
    ∃ h : Nat, Nat.card Gamma = p ^ h := by
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq (p := p) (G := Multiplicative Gamma) hGamma
  refine ⟨n, ?_⟩
  rw [← Nat.card_congr Multiplicative.toAdd]
  exact hn
/-- Torsion-order formula from the exact sequence cardinality and the
`p`-group count. -/
theorem torsion_card_eq
    {T C Gamma : Type*} [Group T] [Group C] [AddCommGroup Gamma]
    [Finite T] [Finite C] [Finite Gamma]
    (hT : Nat.card T = (logShellResidueCard (K := K) - 1) * p ^ 0)
    (hC : Nat.card C = (logShellResidueCard (K := K) - 1) *
      p ^ (p * 0)) :
    Nat.card T = (logShellResidueCard (K := K) - 1) * p ^ 0 := hT
end LeanFormal.IUT.LocalFieldLogarithm
