import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import Mathlib.RingTheory.DiscreteValuationRing.Basic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aValuationActual
open scoped NNReal NormedField
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
variable {E : Type*} [NormedField E] [CharZero E] [CompleteSpace E]
variable [IsUltrametricDist E] [ProperSpace E]
variable {p : Nat} [Fact p.Prime] [NormedAlgebra (Padic p) E]
include p
/-- DVR structure on the actual integer ring of a complete ultrametric finite extension. -/
theorem integers_isDiscreteValuationRing :
    IsDiscreteValuationRing (Integers E) := by
  haveI : Fact p.Prime := inferInstance
  haveI : NormedAlgebra (Padic p) E := inferInstance
  exact isDiscreteValuationRingIntegers (K := E) (p := p)
/-- Actual uniformizer of `Integers E`. -/
noncomputable def uniformizer : Integers E := by
  haveI : Fact p.Prime := inferInstance
  haveI : NormedAlgebra (Padic p) E := inferInstance
  letI : IsDiscreteValuationRing (Integers E) := isDiscreteValuationRingIntegers (K := E) (p := p)
  exact Classical.choose (IsDiscreteValuationRing.exists_prime (Integers E))
#check integers_isDiscreteValuationRing
#check uniformizer
end LeanFormal.IUT.XiFPaper.Node09H1aValuationActual
end