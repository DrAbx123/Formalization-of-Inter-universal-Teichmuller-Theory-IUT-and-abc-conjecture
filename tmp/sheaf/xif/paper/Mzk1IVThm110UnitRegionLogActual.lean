/- Unit-region log relative expression with explicit scale factor. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110UnitRegionScalingActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitRegionLogActual
open MeasureTheory
open LeanFormal.IUT
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure]
/-- The actual scaled unit region is the explicit scale times the canonical unit reference. -/
theorem IQHullUnitRegion_eq_scale_smul :
    arithmeticTupleIQHullUnitRegion places tuple =
      arithmeticTupleIQHullUnitScale places tuple •
        arithmeticTupleCanonicalUnitReference places tuple := rfl
/-- Unit-region log relative to the canonical reference, with the scale kept explicit. -/
theorem unitRegionLog_relative_eq_scale_measure :
    arithmeticTupleIQHullUnitRegionHaarLog places tuple μ -
      Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
        Real.log (μ (arithmeticTupleIQHullUnitRegion places tuple)).toReal -
          Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal := rfl
#check IQHullUnitRegion_eq_scale_smul
#check unitRegionLog_relative_eq_scale_measure
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitRegionLogActual
end
