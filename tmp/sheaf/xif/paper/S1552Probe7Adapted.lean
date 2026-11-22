import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

namespace Probe7
variable (P : NumberField.FinitePlace ℚ)

example : Algebra ℚ (Completion (comap P)) :=
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (R := NumberField.RingOfIntegers ℚ) (K := ℚ) (S := ℚ)
    (v := underlyingPrime (comap P)) (Algebra.id ℚ)

example : Completion (comap P) ≃+* PadicScalarField P := by
  letI : Algebra ℚ (Completion (comap P)) :=
    IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
      (R := NumberField.RingOfIntegers ℚ) (K := ℚ) (S := ℚ)
      (v := underlyingPrime (comap P)) (Algebra.id ℚ)
  exact (rationalCompletionPadicEquiv P).toRingEquiv

end Probe7
