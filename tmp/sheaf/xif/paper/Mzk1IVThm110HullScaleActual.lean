/- Relative hull log: unknown unit-reference normalization cancels. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110HullUnitZeroActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110HullScaleActual
open MeasureTheory
open LeanFormal.IUT
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure]
/-- Relative hull log: hull log minus canonical unit reference log equals the
unit-relative hull volume.  The unknown scale normalization cancels. -/
theorem hullLog_relative_eq_hullUnitLog :
    arithmeticTupleCanonicalHullHaarLog places tuple μ -
      Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
        arithmeticTupleHullUnitLogVolume places tuple := by
  rw [arithmeticTupleCanonicalHullHaarLog,
    arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal]
  ring
#check hullLog_relative_eq_hullUnitLog
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110HullScaleActual
end
