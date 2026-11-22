import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aAbstractDVRValuationActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal
variable {p : Nat} [Fact p.Prime] {J : Type} [Fintype J]
variable (E : J → Type)
variable [∀ j, NontriviallyNormedField (E j)]
variable [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)]
variable [∀ j, CompleteSpace (E j)] [∀ j, IsUltrametricDist (E j)]
local instance charZeroE (j : J) : CharZero (E j) :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] (E j)).injective
local instance properE (j : J) : ProperSpace (E j) :=
  FiniteDimensional.proper ℚ_[p] (E j)
local instance normedAlgebraE (j : J) : NormedAlgebra (Padic p) (E j) :=
  inferInstance
local instance dvrE (j : J) : IsDiscreteValuationRing (Integers (E j)) :=
  isDiscreteValuationRingIntegers
/-- The abstract factor valuation on E j. -/
noncomputable def factorValuation (j : J) :
    Valuation (E j) (WithZero (Multiplicative Int)) :=
  (IsDiscreteValuationRing.maximalIdeal (Integers (E j))).valuation (E j)
#check factorValuation
end LeanFormal.IUT.XiFPaper.Node09H1aAbstractDVRValuationActual
end