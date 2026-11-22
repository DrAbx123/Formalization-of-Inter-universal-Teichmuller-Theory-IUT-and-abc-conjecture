/- Port of local-cft-port's uniformizer API to the repository's Integers: existence of a
uniformizer (addVal = 1) in the integer ring of a finite extension of Q_p. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalUniformizerActual

open LeanFormal.IUT.LocalFieldIntegralUnits

variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
  [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
  [IsDiscreteValuationRing (Integers L)]

/-- Every finite extension of Q_p has a uniformizer in its norm-integer ring. -/
theorem exists_uniformizer_integers :
    ∃ pi : Integers L, IsDiscreteValuationRing.addVal (Integers L) pi = 1 := by
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible (R := Integers L)
  exact ⟨pi, IsDiscreteValuationRing.addVal_uniformizer hpi⟩

/-- The additive order of a uniformizer is one. -/
theorem addVal_uniformizer_eq_one (pi : Integers L)
    (hpi : Irreducible pi) :
    IsDiscreteValuationRing.addVal (Integers L) pi = 1 :=
  IsDiscreteValuationRing.addVal_uniformizer hpi

#print axioms exists_uniformizer_integers
#print axioms addVal_uniformizer_eq_one
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalUniformizerActual
