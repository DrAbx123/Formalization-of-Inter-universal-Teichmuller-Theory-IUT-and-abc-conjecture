import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import LeanFormal.IUT.ABCBridge.Geometry.RationalCommonPrimeFinrank

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

namespace Probe9
variable (P : NumberField.FinitePlace ℚ)

local instance instAlgebraRatCompletionAux : Algebra ℚ (Completion (comap P)) :=
  @IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (NumberField.RingOfIntegers ℚ) _ _ ℚ ℚ _ _ _ _ (underlyingPrime (comap P)) (Algebra.id ℚ)

example : Completion (comap P) ≃+* PadicScalarField P :=
  AlgEquiv.toRingEquiv (rationalCompletionPadicEquiv P)

example : Continuous (rationalCompletionPadicEquiv P) :=
  (rationalCompletionPadicEquiv P).continuous

example : Continuous (rationalCompletionPadicEquiv P).symm :=
  (rationalCompletionPadicEquiv P).symm.continuous

example : Function.Injective (rationalCompletionPadicEquiv P) :=
  (rationalCompletionPadicEquiv P).injective

example : Function.Surjective (rationalCompletionPadicEquiv P) :=
  (rationalCompletionPadicEquiv P).surjective

end Probe9
