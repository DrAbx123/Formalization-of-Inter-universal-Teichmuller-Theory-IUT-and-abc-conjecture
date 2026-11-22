import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterfaceScaledUnit
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedLogVolume
open scoped Pointwise
/-! Corrected reduction: the attempted unconditional hullUnitLog=0 is FALSE as stated.

`arithmeticTupleIQHullUnitRegion = arithmeticTupleIQHullUnitScale • canonicalUnitReference`,
so the green inequality `hullLog <= IQHullUnitRegionLog` is NOT comparable with the
green decomposition `hullLog = hullUnitLog + canonicalUnitReferenceLog` unless the
scale is 1.  We prove the conditional identity and record the exact missing scale
relation instead of asserting a false equality. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110HullUnitZeroActual
open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure]
/-- If the compactness scale is 1, the IQ unit region is the canonical unit reference. -/
theorem IQHullUnitRegion_eq_unitReference_of_scale_one
    (hscale : arithmeticTupleIQHullUnitScale places tuple = 1) :
    arithmeticTupleIQHullUnitRegion places tuple =
      arithmeticTupleCanonicalUnitReference places tuple := by
  unfold arithmeticTupleIQHullUnitRegion
  rw [hscale, one_smul]
/-- Conditional actual identity: scale 1 implies hullUnitLog = 0. -/
theorem arithmeticTupleHullUnitLogVolume_eq_zero_of_scale_one
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure]
    (hscale : arithmeticTupleIQHullUnitScale places tuple = 1) :
    arithmeticTupleHullUnitLogVolume places tuple = 0 := by
  have hrel := arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal
    (places := places) (tuple := tuple) μ
  have hle := arithmeticTupleCanonicalHullHaarLog_le_unitRegionHaarLog
    (places := places) (tuple := tuple) μ
  have hunit := IQHullUnitRegion_eq_unitReference_of_scale_one (places := places) (tuple := tuple) hscale
  have hnonneg := arithmeticTupleHullUnitLogVolume_nonneg (places := places) (tuple := tuple)
  simp only [arithmeticTupleCanonicalHullHaarLog, arithmeticTupleIQHullUnitRegionHaarLog,
    hunit] at hrel hle
  linarith
/-- Conditional actual identity: scale 1 implies hullLog = unitRegionLog. -/
theorem arithmeticTupleCanonicalHullHaarLog_eq_unitRegion_of_scale_one
    (hscale : arithmeticTupleIQHullUnitScale places tuple = 1) :
    arithmeticTupleCanonicalHullHaarLog places tuple μ =
      arithmeticTupleIQHullUnitRegionHaarLog places tuple μ := by
  have hrel := arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal
    (places := places) (tuple := tuple) μ
  have hzero := arithmeticTupleHullUnitLogVolume_eq_zero_of_scale_one
    (places := places) (tuple := tuple) μ hscale
  have hunit := IQHullUnitRegion_eq_unitReference_of_scale_one (places := places) (tuple := tuple) hscale
  simp only [arithmeticTupleCanonicalHullHaarLog, arithmeticTupleIQHullUnitRegionHaarLog,
    hunit] at hrel ⊢
  rw [hzero] at hrel
  linarith
/-- Exact obstruction: the unconditional statement needs the scale relation, not scale=1. -/
def hullUnitZeroObstruction : List String :=
  [ "arithmeticTupleIQHullUnitRegion = arithmeticTupleIQHullUnitScale • canonicalUnitReference",
    "hullLog <= IQHullUnitRegionLog compares against scaled unit reference",
    "hullLog = hullUnitLog + canonicalUnitReferenceLog decomposes against canonical unit reference",
    "unconditional hullUnitLog = 0 is not derivable; exact missing relation is the scale log formula" ]
theorem hullUnitZeroObstruction_length : hullUnitZeroObstruction.length = 4 := rfl
#check arithmeticTupleHullUnitLogVolume_eq_zero_of_scale_one
#check arithmeticTupleCanonicalHullHaarLog_eq_unitRegion_of_scale_one
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110HullUnitZeroActual
end
