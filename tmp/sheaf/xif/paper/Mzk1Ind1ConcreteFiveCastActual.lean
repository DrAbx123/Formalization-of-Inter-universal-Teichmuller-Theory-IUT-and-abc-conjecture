import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1ConcreteFiveCastActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem concreteFiveCompletion_eq :
    NumberFieldFinitePlace.Completion concreteFivePlace =
      concreteFiveHeightOne.adicCompletion ℚ := by
  rw [NumberFieldFinitePlace.Completion, concreteFivePlace_underlyingPrime]

#print axioms concreteFiveCompletion_eq
end LeanFormal.IUT.XiFPaper.Mzk1Ind1ConcreteFiveCastActual