import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import LeanFormal.IUT.ABCBridge.Geometry.RationalCommonPrimeFinrank

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

namespace Probe10
variable (P : NumberField.FinitePlace ℚ)

local instance instAlgebraRatCompletionAux : Algebra ℚ (Completion P) :=
  @IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (NumberField.RingOfIntegers ℚ) _ _ ℚ ℚ _ _ _ _ P.maximalIdeal (Algebra.id ℚ)

local instance factTargetPrime : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).property⟩

example : Completion P ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val] :=
  AlgEquiv.toRingEquiv (R := ℚ) (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal)

example : Continuous (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal).continuous

example : Continuous (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal).symm :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal).symm.continuous

end Probe10
