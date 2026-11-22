import tmp.sheaf.xif.paper.S2590PadicSingletonNullActual
import tmp.sheaf.xif.paper.S2594HpointWiringActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2587Cor312PointMapSkeletonActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2589DictionaryMinimalActual
open LeanFormal.IUT.XiFPaper.S2590PadicSingletonNullActual
open LeanFormal.IUT.XiFPaper.S2594HpointWiringActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2595UnconditionalDictionaryActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

theorem S2595Dictionary :
    S2587PointHeightDictionary
      (S2586IQHullLogVolumeInterface T b) (S2588PointMap T b) :=
  S2589CurrentDictionary_of_singleton_null T b (S2590SingletonNull T b)

#check S2595Dictionary
#print axioms S2595Dictionary

/-- Unconditional hpoint: the singleton-null measure gap is discharged by
S2590.  Only the frozen H1 valuation input remains. -/
theorem S2595_hpoint {eps : Real} (heps : 0 <= eps)
    (hval : forall a n c : Nat, IsABCTriple a n c ->
      forall q : Nat, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) ->
        max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) <= 1 + eps) :
    forall a n c : Nat, IsABCTriple a n c ->
      ((S2586IQHullLogVolumeInterface T b).logVolume
        {(S2586IQHullLogVolumeInterface T b).scaleShift
          (S2588PointMap T b a n c)}).toReal <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) :=
  S2594_pointBound T b (S2590SingletonNull T b) heps hval

#check S2595_hpoint
#print axioms S2595_hpoint
end LeanFormal.IUT.XiFPaper.S2595UnconditionalDictionaryActual
end