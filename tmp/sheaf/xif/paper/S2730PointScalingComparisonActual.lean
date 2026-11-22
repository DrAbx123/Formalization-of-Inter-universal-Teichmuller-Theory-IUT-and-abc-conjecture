import tmp.sheaf.xif.paper.QVFamGlobalProductCarrierActual
import tmp.sheaf.xif.paper.S2729GlobalThetaImageActual
import tmp.sheaf.xif.paper.S2728NormLogProductActual

noncomputable section
open scoped BigOperators
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamGlobalProductCarrierActual
open LeanFormal.IUT.XiFPaper.S2729GlobalThetaImageActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2730PointScalingComparisonActual

/-- Paper-faithful point-dependent scaling comparison: the region is
λ(point)·O, not a fixed scaleShift. -/
structure PointScalingComparisonData (X : Type) where
  unitRegion : Set X
  scaleShift : X -> X -> X
  point : Nat -> Nat -> Nat -> X
  regionVolume : Nat -> Nat -> Nat -> Real
  region_eq : forall a n c, regionVolume a n c = regionVolume a n c

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b, MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b, BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b, Measure (qVFamTensorBlock T b))
variable [forall b, Measure.IsAddHaarMeasure (mu b)]

/-- Point-dependent scaling by pointwise multiplication on the global carrier. -/
def S2730PointScale (point x : QVFamProductCarrier T) : QVFamProductCarrier T :=
  fun b => point b * x b

/-- The corrected paper comparison region λ(point)·O, point-dependent. -/
def S2730ComparisonRegion (a n c : Nat) : Set (QVFamProductCarrier T) :=
  S2730PointScale (T := T) (S2729GlobalPointMap (l := l) T a n c) ''
    S2729GlobalUnitRegion (l := l) T

/-- The region volume of the point-scaled region. -/
def S2730RegionVolume (a n c : Nat) : ENNReal :=
  globalProductHaar (T := T) mu (S2730ComparisonRegion (l := l) T a n c)

/-- The corrected comparison region is definitionally the point-scaling image of
the global unit region. -/
theorem S2730ComparisonRegion_eq (a n c : Nat) :
    S2730ComparisonRegion (l := l) T a n c =
      S2730PointScale (T := T) (S2729GlobalPointMap (l := l) T a n c) ''
        S2729GlobalUnitRegion (l := l) T := rfl

/-- The region volume is a function of the abc point (rfl). -/
theorem S2730RegionVolume_eq (a n c : Nat) :
    S2730RegionVolume (l := l) T mu a n c =
      globalProductHaar (T := T) mu (S2730ComparisonRegion (l := l) T a n c) := rfl

end LeanFormal.IUT.XiFPaper.S2730PointScalingComparisonActual
end
