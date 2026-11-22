import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aMaximalIdealValuationActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal
variable {p : Nat} [Fact p.Prime] {J : Type} [Fintype J]
variable (E : J → Type)
variable [∀ j, NontriviallyNormedField (E j)]
variable [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)]
variable [∀ j, CompleteSpace (E j)] [∀ j, IsUltrametricDist (E j)]
/-- The abstract factor valuation from the DVR maximal ideal. -/
noncomputable def factorValuation (j : J) :
    Valuation (E j) (WithZero (Multiplicative Int)) := by
  letI : CharZero (E j) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[p] (E j)).injective
  letI : ProperSpace (E j) := FiniteDimensional.proper ℚ_[p] (E j)
  letI : IsDiscreteValuationRing (Integers (E j)) :=
    isDiscreteValuationRingIntegers (K := E j) (p := p)
  exact (IsDiscreteValuationRing.maximalIdeal (Integers (E j))).valuation (E j)
#check factorValuation
end LeanFormal.IUT.XiFPaper.Node09H1aMaximalIdealValuationActual
end