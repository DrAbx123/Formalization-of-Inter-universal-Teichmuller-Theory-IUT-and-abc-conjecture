import tmp.sheaf.xif.paper.S2586IQHullLogVolumeInstantiationActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2587Cor312PointMapSkeletonActual

universe u

/-- The point-height dictionary specialized to an arbitrary actual
`IQHullLogVolumeInterface` carrier. -/
def S2587PointHeightDictionary {X : Type u} (W : IQHullLogVolumeInterface X)
    (p : Nat -> Nat -> Nat -> X) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    (W.logVolume {W.scaleShift (p a b c)}).toReal <=
      Height.logHeight₁ (abcRationalPoint a c)

/-- Point-map data for the actual tensor-block carrier. -/
structure S2587PointwisePointData
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)] where
  point : Nat -> Nat -> Nat -> qVFamTensorBlock T b
  dictionary : S2587PointHeightDictionary
    (S2586IQHullLogVolumeInterface T b) point

def S2587PointMapGap
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)] : Prop :=
  Nonempty (S2587PointwisePointData T b)

#check S2587PointHeightDictionary
#check S2587PointwisePointData
#check S2587PointMapGap

end LeanFormal.IUT.XiFPaper.S2587Cor312PointMapSkeletonActual
end