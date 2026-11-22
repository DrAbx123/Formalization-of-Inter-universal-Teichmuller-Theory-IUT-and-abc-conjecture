import tmp.sheaf.xif.paper.Mzk1GaloisRingBridgeActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeNormalizedCompletion

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1GaloisRingBridgeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

namespace LeanFormal.IUT.XiFPaper.ProbeScalarTowerActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev pNat := (completionRationalPrime (nativeBadToKPlace T b)).val
abbrev lowerPlace := LeanFormal.IUT.NumberFieldFinitePlace.comap (k := T.arithmetic.F) (nativeBadToKPlace T b)
abbrev upperPlace := nativeBadToKPlace T b

def kPlaceAtPrime : FinitePlaceAtPrime T.arithmetic.K (pNat T b) :=
  ⟨nativeBadToKPlace T b, rfl⟩

example : IsScalarTower ℚ_[pNat T b]
    (lowerPlace T b).maximalIdeal.adicCompletion T.arithmetic.F
    (upperPlace T b).maximalIdeal.adicCompletion T.arithmetic.K := by
  have hprime : completionRationalPrime (lowerPlace T b : NumberField.FinitePlace T.arithmetic.F) =
      completionRationalPrime (upperPlace T b : NumberField.FinitePlace T.arithmetic.K) := by
    rw [completionRationalPrime_comap]
  letI algLower : Algebra (PadicScalarField (lowerPlace T b : NumberField.FinitePlace T.arithmetic.F))
      ((lowerPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) :=
    normalizedCompletionAlgebra (K := T.arithmetic.F) (lowerPlace T b)
  letI algUpper : Algebra (PadicScalarField (upperPlace T b : NumberField.FinitePlace T.arithmetic.K))
      ((upperPlace T b).maximalIdeal.adicCompletion T.arithmetic.K) :=
    normalizedCompletionAlgebra (K := T.arithmetic.K) (upperPlace T b)
  letI : Algebra ℚ_[pNat T b] ((lowerPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) :=
    (congrArg PadicScalarField hprime.symm) ▸ algLower
  letI : Algebra ℚ_[pNat T b] ((upperPlace T b).maximalIdeal.adicCompletion T.arithmetic.K) :=
    (congrArg PadicScalarField hprime.symm) ▸ algUpper
  letI : SMul ℚ_[pNat T b] ((lowerPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) :=
    (inferInstance : Algebra ℚ_[pNat T b] _).toSMul
  letI : SMul ℚ_[pNat T b] ((upperPlace T b).maximalIdeal.adicCompletion T.arithmetic.K) :=
    (inferInstance : Algebra ℚ_[pNat T b] _).toSMul
  change IsScalarTower ℚ_[pNat T b]
    (CommonPrimeCompletion (relativeCommonPrimePlace (k := T.arithmetic.F) (kPlaceAtPrime T b)))
    (CommonPrimeCompletion (kPlaceAtPrime T b))
  infer_instance

end LeanFormal.IUT.XiFPaper.ProbeScalarTowerActual
end
