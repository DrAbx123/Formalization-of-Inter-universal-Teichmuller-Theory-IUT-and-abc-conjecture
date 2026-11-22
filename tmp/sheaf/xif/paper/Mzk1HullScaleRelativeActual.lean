/- Relative hull log: unknown unit-reference normalization cancels. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterfaceScaledUnit
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedLogVolume
import tmp.sheaf.xif.paper.Mzk1IVThm110HullUnitZeroActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullScaleRelativeActual
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure]
theorem hullLog_relative_eq_hullUnitLog :
    arithmeticTupleCanonicalHullHaarLog places tuple μ -
      Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
        arithmeticTupleHullUnitLogVolume places tuple := by
  rw [arithmeticTupleCanonicalHullHaarLog,
    arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal]
  ring
#check hullLog_relative_eq_hullUnitLog
end LeanFormal.IUT.XiFPaper.Mzk1HullScaleRelativeActual
end
