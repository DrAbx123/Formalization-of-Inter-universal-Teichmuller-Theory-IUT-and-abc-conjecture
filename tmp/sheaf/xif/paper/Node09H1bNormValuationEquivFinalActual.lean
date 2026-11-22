import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1bNormValuationEquivFinalActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open scoped NNReal
variable {p : Nat} [Fact p.Prime] {J : Type} [Fintype J]
variable (E : J → Type)
variable [∀ j, NontriviallyNormedField (E j)]
variable [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)]
variable [∀ j, CompleteSpace (E j)] [∀ j, IsUltrametricDist (E j)]
/-- Norm valuation and DVR maximal-ideal valuation are equivalent. -/
theorem normValuation_isEquiv_maximalIdealValuation
    (p : Nat) [Fact p.Prime] (j : J)
    [hDVR : IsDiscreteValuationRing (Integers (E j))]
    [hfrac : IsFractionRing (Integers (E j)) (E j)] :
    (NormedField.valuation (K := E j)).IsEquiv
      ((IsDiscreteValuationRing.maximalIdeal (Integers (E j))).valuation (E j)) := by
  letI : CharZero (E j) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[p] (E j)).injective
  letI : ProperSpace (E j) := FiniteDimensional.proper ℚ_[p] (E j)
  set v : Valuation (E j) (WithZero (Multiplicative Int)) :=
    (IsDiscreteValuationRing.maximalIdeal (Integers (E j))).valuation (E j)
  have hsub : v.valuationSubring.toSubring = Integers (E j) := by
    rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
      (A := Integers (E j)) (K := E j)]
    ext x
    constructor
    · rintro ⟨a, -, rfl⟩
      exact a.property
    · intro hx
      exact ⟨⟨x, hx⟩, Subring.mem_top _, rfl⟩
  apply Valuation.isEquiv_of_val_le_one
  intro x
  have hnorm : (NormedField.valuation (K := E j)) x ≤ 1 ↔
      x ∈ Integers (E j) := by
    rw [NormedField.v_eq_valuation]
    rw [← Valued.toNormedField.norm_le_one_iff (L := E j) (x := x)]
    exact mem_integers_iff x
  have hmax : v x ≤ 1 ↔ x ∈ Integers (E j) := by
    rw [← Valuation.mem_valuationSubring_iff]
    change x ∈ (v.valuationSubring.toSubring : Subring (E j))
    rw [hsub]
  exact hnorm.trans hmax.symm
#check normValuation_isEquiv_maximalIdealValuation
end LeanFormal.IUT.XiFPaper.Node09H1bNormValuationEquivFinalActual
end