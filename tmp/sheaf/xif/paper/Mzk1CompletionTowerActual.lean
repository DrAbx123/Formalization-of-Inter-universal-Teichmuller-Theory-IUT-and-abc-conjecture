import tmp.sheaf.xif.paper.Mzk1GaloisRingBridgeActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeNormalizedCompletion

/-! # Actual Qp scalar tower for the chosen completion pair

Uses the normalized/CommonPrimeCompletion donor tower at the same rational prime.
-/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1GaloisRingBridgeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

namespace LeanFormal.IUT.XiFPaper.Mzk1CompletionTowerActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev pNat := (completionRationalPrime (nativeBadToKPlace T b)).val

abbrev upperPlace : NumberField.FinitePlace T.arithmetic.K := nativeBadToKPlace T b
abbrev lowerPlace : NumberField.FinitePlace T.arithmetic.F :=
  LeanFormal.IUT.NumberFieldFinitePlace.comap (k := T.arithmetic.F) (nativeBadToKPlace T b)

def upperPlaceAtPrime : FinitePlaceAtPrime T.arithmetic.K (pNat T b) :=
  ⟨upperPlace T b, rfl⟩

theorem commonPrimeTower_scalarTower :
    IsScalarTower ℚ_[pNat T b]
      (CommonPrimeCompletion
        (relativeCommonPrimePlace (k := T.arithmetic.F) (upperPlaceAtPrime T b)))
      (CommonPrimeCompletion (upperPlaceAtPrime T b)) :=
  relativeNormalizedCompletionScalarTower (k := T.arithmetic.F) (upperPlaceAtPrime T b)

theorem commonPrimeTower_moduleFinite :
    Module.Finite
      (CommonPrimeCompletion
        (relativeCommonPrimePlace (k := T.arithmetic.F) (upperPlaceAtPrime T b)))
      (CommonPrimeCompletion (upperPlaceAtPrime T b)) :=
  relativeNormalizedCompletionFinite (k := T.arithmetic.F) (upperPlaceAtPrime T b)



end LeanFormal.IUT.XiFPaper.Mzk1CompletionTowerActual
end
