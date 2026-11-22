import tmp.sheaf.xif.paper.QVFamGlobalProductCarrierActual
import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import tmp.sheaf.xif.paper.S2725ThetaImageHullActual
import tmp.sheaf.xif.paper.S2728NormLogProductActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull

noncomputable section
open scoped BigOperators
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamGlobalProductCarrierActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2725ThetaImageHullActual
open LeanFormal.IUT.ABCBridge
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2729GlobalThetaImageActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b, MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b, BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b, Measure (qVFamTensorBlock T b))
variable [∀ b, Measure.IsAddHaarMeasure (mu b)]

def S2729GlobalPointMap (a n c : Nat) : QVFamProductCarrier T :=
  fun b => S2588PointMap (l := l) T b a n c

def S2729GlobalThetaImage : Set (QVFamProductCarrier T) :=
  Set.range (fun p : Nat × Nat × Nat => S2729GlobalPointMap (l := l) T p.1 p.2.1 p.2.2)

def S2729GlobalUnitRegion : Set (QVFamProductCarrier T) :=
  Set.pi Set.univ (fun b =>
    arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple)

def S2729GlobalComparisonRegion (a n c : Nat) : Set (QVFamProductCarrier T) :=
  (id : QVFamProductCarrier T → QVFamProductCarrier T) ''
    (S2729GlobalUnitRegion T ∪ {S2729GlobalPointMap (l := l) T a n c})

def S2729Hweightvol : Prop :=
  ∀ a n c : Nat, IsABCTriple a n c →
    arithmeticWeight (abcRationalPoint a c) ≤
      (globalProductHaar (T := T) mu
        (S2729GlobalComparisonRegion (l := l) T a n c)).toReal

theorem S2729GlobalComparisonRegion_eq (a n c : Nat) :
    S2729GlobalComparisonRegion (l := l) T a n c =
      S2729GlobalUnitRegion T ∪ {S2729GlobalPointMap (l := l) T a n c} := by
  simp [S2729GlobalComparisonRegion]

theorem S2729GlobalPoint_mem_region (a n c : Nat) :
    S2729GlobalPointMap (l := l) T a n c ∈
      S2729GlobalComparisonRegion (l := l) T a n c := by
  simp [S2729GlobalComparisonRegion, S2729GlobalUnitRegion]

theorem S2729Hweightvol_iff :
    S2729Hweightvol (l := l) T mu ↔
      ∀ a n c : Nat, IsABCTriple a n c →
        arithmeticWeight (abcRationalPoint a c) ≤
          (globalProductHaar (T := T) mu
            (S2729GlobalComparisonRegion (l := l) T a n c)).toReal :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S2729GlobalThetaImageActual
end
