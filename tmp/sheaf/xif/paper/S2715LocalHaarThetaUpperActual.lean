import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSharpUpperBound

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2715LocalHaarThetaUpperActual

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

/-- The canonical theta constant attached to the unit-region Haar mass and an
arbitrary q: `theta / |log q|`.  This is the exact constant that makes the
local Haar upper bound a theta-pilot upper estimate. -/
noncomputable def S2715CTheta
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] (q : Real) : Real :=
  arithmeticTupleIQHullUnitRegionHaarLog places tuple μ / |Real.log q|

/-- Actual composition: normalized hull log-volume <= unit-region log-volume
= CTheta * |log q|, with CTheta defined by the ratio. -/
theorem S2715HullLog_le_CTheta_mul_absLog
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] {q : Real}
    (hq : |Real.log q| ≠ 0) :
    arithmeticTupleCanonicalHullHaarLog places tuple μ <=
      S2715CTheta places tuple μ q * |Real.log q| := by
  have hle := arithmeticTupleCanonicalHullHaarLog_le_unitRegionHaarLog
    places tuple μ
  dsimp [S2715CTheta]
  rw [div_mul_cancel₀ _ hq]
  exact hle

/-- Normalized unit region (mass one): theta = 0, so the hull bound is the
no-hypothesis upper estimate with CTheta = 0. -/
theorem S2715HullLog_le_zero_mul_absLog_of_unitRegion_measure_one
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] {q : Real}
    (hunit : μ (arithmeticTupleIQHullUnitRegion places tuple) = 1) :
    arithmeticTupleCanonicalHullHaarLog places tuple μ <=
      (0 : Real) * |Real.log q| := by
  rw [zero_mul]
  exact arithmeticTupleCanonicalHullHaarLog_nonpos_of_unitRegion_measure_one
    places tuple μ hunit

#print axioms S2715HullLog_le_CTheta_mul_absLog
#print axioms S2715HullLog_le_zero_mul_absLog_of_unitRegion_measure_one

end LeanFormal.IUT.XiFPaper.S2715LocalHaarThetaUpperActual
end
