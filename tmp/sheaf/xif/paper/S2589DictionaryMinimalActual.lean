import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import tmp.sheaf.xif.paper.S2587Cor312PointMapSkeletonActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312GapDictionaryLayer

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2587Cor312PointMapSkeletonActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2589DictionaryMinimalActual

/-- The only measure-theoretic input needed for the minimal dictionary: an
additive Haar measure on the tensor block has no atoms. -/
def S2589SingletonNull {X : Type u} (W : IQHullLogVolumeInterface X) : Prop :=
  forall x : X, W.logVolume {x} = 0

theorem S2587PointHeightDictionary_of_singleton_null
    {X : Type u} (W : IQHullLogVolumeInterface X)
    (p : Nat -> Nat -> Nat -> X) (hnull : S2589SingletonNull W) :
    S2587PointHeightDictionary W p := by
  intro a b c habc
  rw [hnull (W.scaleShift (p a b c))]
  simp only [ENNReal.toReal_zero]
  exact cor312GapDict_abcRationalPoint_logHeight₁_nonneg habc

theorem S2589CurrentDictionary_of_singleton_null
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)]
    (hnull : S2589SingletonNull
      (S2586IQHullLogVolumeInterface T b)) :
    S2587PointHeightDictionary
      (S2586IQHullLogVolumeInterface T b) (S2588PointMap T b) :=
  S2587PointHeightDictionary_of_singleton_null
    (S2586IQHullLogVolumeInterface T b) (S2588PointMap T b) hnull

#check S2589SingletonNull
#check S2587PointHeightDictionary_of_singleton_null
#check S2589CurrentDictionary_of_singleton_null

end LeanFormal.IUT.XiFPaper.S2589DictionaryMinimalActual
end