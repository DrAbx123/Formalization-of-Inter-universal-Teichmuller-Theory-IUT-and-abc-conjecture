/- Unit-region log relative expression with explicit scale factor. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterfaceScaledUnit
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSharpUpperBound
import tmp.sheaf.xif.paper.Mzk1IVThm110UnitRegionScalingActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1UnitRegionLogRelativeActual
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped Pointwise
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure]
theorem IQHullUnitRegion_eq_scale_smul :
    arithmeticTupleIQHullUnitRegion places tuple =
      arithmeticTupleIQHullUnitScale places tuple •
        arithmeticTupleCanonicalUnitReference places tuple := rfl
theorem unitRegionLog_eq_scale_smul_log :
    arithmeticTupleIQHullUnitRegionHaarLog places tuple μ =
      Real.log (μ (arithmeticTupleIQHullUnitScale places tuple •
        arithmeticTupleCanonicalUnitReference places tuple)).toReal := rfl
#check IQHullUnitRegion_eq_scale_smul
#check unitRegionLog_eq_scale_smul_log
end LeanFormal.IUT.XiFPaper.Mzk1UnitRegionLogRelativeActual
end
