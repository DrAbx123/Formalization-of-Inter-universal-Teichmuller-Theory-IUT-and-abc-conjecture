import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2689Place2161Actual

local instance : Fact (Nat.Prime 2161) := ⟨by norm_num⟩

local instance : Fact (Irreducible
    (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

noncomputable def S2689GaussianPlace2161 : NumberField.FinitePlace GaussianField :=
  Classical.choose (NumberFieldFinitePlace.comap_surjective
    (k := ℚ) (K := GaussianField)
    (LeanFormal.IUT.rationalFinitePlace 2161))

theorem S2689GaussianPlace2161_comap :
    NumberFieldFinitePlace.comap (k := ℚ) S2689GaussianPlace2161 =
      LeanFormal.IUT.rationalFinitePlace 2161 :=
  Classical.choose_spec (NumberFieldFinitePlace.comap_surjective
    (k := ℚ) (K := GaussianField)
    (LeanFormal.IUT.rationalFinitePlace 2161))

#check S2689GaussianPlace2161
#check S2689GaussianPlace2161_comap
#print axioms S2689GaussianPlace2161_comap

end LeanFormal.IUT.XiFPaper.S2689Place2161Actual
end