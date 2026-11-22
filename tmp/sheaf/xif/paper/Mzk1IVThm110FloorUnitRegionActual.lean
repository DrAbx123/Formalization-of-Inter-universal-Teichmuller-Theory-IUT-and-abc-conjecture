import tmp.sheaf.xif.paper.Mzk1IVThm110HullUnitZeroActual
import tmp.sheaf.xif.paper.Mzk1IVThm110FloorNativeHullActual
import tmp.sheaf.xif.paper.Mzk1IVThm110UnitRegionScalingActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorUnitRegionActual
open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312FloorActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorNativeHullActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HullUnitZeroActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (label : Type) [Fintype label] [Nonempty label]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure]
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- scale=1: unit-region log=-M and M>=1 give floor qSigned = native qSigned. -/
theorem floorQSigned_eq_native_of_unitRegion
    (hscale1 : arithmeticTupleIQHullUnitScale places tuple = 1)
    (hM : arithmeticTupleIQHullUnitRegionHaarLog places tuple μ =
      -nativeGlobalQPilotNormalizedLogMagnitude T)
    (hMone : 1 ≤ nativeGlobalQPilotNormalizedLogMagnitude T) :
    (signedFloorCertificate (places := places) (tuple := tuple) label μ).qSigned =
      S3013QSigned T := by
  have hhull : arithmeticTupleCanonicalHullHaarLog places tuple μ =
      -nativeGlobalQPilotNormalizedLogMagnitude T :=
    (arithmeticTupleCanonicalHullHaarLog_eq_unitRegion_of_scale_one
      (p := p) places tuple μ hscale1).trans hM
  exact floorQSigned_eq_native_of_hull (p := p) (places := places) (tuple := tuple)
    (label := label) (μ := μ) (T := T) hhull hMone
/-- scale != 1 exact gap: hullUnitLog or full Haar scaling relation. -/
def scaleNeOneGap : List String :=
  [ "scale != 1: need arithmeticTupleHullUnitLogVolume places tuple = 0",
    "or full unitRegionLog = canonicalUnitReferenceLog + D*log‖scale‖ plus hullLog relation" ]
theorem scaleNeOneGap_length : scaleNeOneGap.length = 2 := rfl
#check floorQSigned_eq_native_of_unitRegion
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorUnitRegionActual
end