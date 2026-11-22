import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual

namespace Probe5

variable (P : NumberField.FinitePlace ℚ)

example : comap (k := ℚ) P = P := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal]
  change Ideal.comap (RingHom.id (NumberField.RingOfIntegers ℚ)) P.maximalIdeal.asIdeal =
    P.maximalIdeal.asIdeal
  rw [Ideal.comap_id]

#check (rationalCompletionPadicEquiv P)
#check (rationalCompletionPadicEquiv P : Completion (comap P) ≃+* PadicScalarField P)
#check ((rationalCompletionPadicEquiv P : Completion (comap P) ≃+* PadicScalarField P) :
    Completion (comap P) →+* PadicScalarField P)
#check (completionRationalPrime P)
example : completionRationalPrime P = Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal := by
  unfold completionRationalPrime
  rw [show comap (k := ℚ) P = P from by
    apply NumberField.FinitePlace.maximalIdeal_injective
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [NumberFieldFinitePlace.comap_maximalIdeal]
    change Ideal.comap (RingHom.id (NumberField.RingOfIntegers ℚ)) P.maximalIdeal.asIdeal =
      P.maximalIdeal.asIdeal
    rw [Ideal.comap_id]]

end Probe5
