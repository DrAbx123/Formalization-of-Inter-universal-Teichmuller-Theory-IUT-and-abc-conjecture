import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSharpUpperBound

/-!
# Signed real Haar log-volumes of the actual tuple hull and unit region

The `ENNReal`-valued `haarLogVolume` is sign-blind: negative real log-volumes
become `ENNReal.ofReal (-x) = 0`.  The Step-XI comparison, however, is a
signed comparison of log-volumes.  This file records the real-valued logs

* `arithmeticTupleCanonicalHullHaarLog`,
* `arithmeticTupleIQHullUnitRegionHaarLog`,

and proves the genuine signed inequality
`log (mu hull) <= log (mu unitRegion)` from `hull <= unitRegion`.  It also
records the exact `ENNReal`-to-real bridge on finite regions.  No source
`1,circ U` construction or source q comparison is claimed.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory
open scoped Pointwise

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)

variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

/-- The signed real Haar log-volume of the actual canonical hull. -/
def arithmeticTupleCanonicalHullHaarLog
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] : Real :=
  Real.log (μ (arithmeticTupleCanonicalHull places tuple)).toReal

/-- The signed real Haar log-volume of the scaled integral unit region. -/
def arithmeticTupleIQHullUnitRegionHaarLog
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] : Real :=
  Real.log (μ (arithmeticTupleIQHullUnitRegion places tuple)).toReal

theorem arithmeticTupleCanonicalHull_measure_pos
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    0 < μ (arithmeticTupleCanonicalHull places tuple) :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ).1.1

theorem arithmeticTupleCanonicalHull_measure_lt_top_forSignedLog
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    μ (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ).1.2

theorem arithmeticTupleCanonicalHull_measure_ne_zero
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    μ (arithmeticTupleCanonicalHull places tuple) ≠ 0 :=
  (arithmeticTupleCanonicalHull_measure_pos places tuple μ).ne'

theorem arithmeticTupleCanonicalHull_measure_ne_top
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    μ (arithmeticTupleCanonicalHull places tuple) ≠ ⊤ :=
  (arithmeticTupleCanonicalHull_measure_lt_top_forSignedLog places tuple μ).ne

theorem arithmeticTupleCanonicalHull_measure_toReal_pos
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    0 < (μ (arithmeticTupleCanonicalHull places tuple)).toReal :=
  ENNReal.toReal_pos
    (arithmeticTupleCanonicalHull_measure_ne_zero places tuple μ)
    (arithmeticTupleCanonicalHull_measure_ne_top places tuple μ)

omit [BorelSpace (ArithmeticTensorTupleBlock places tuple)] in
theorem arithmeticTupleCanonicalHull_measure_le_unitRegion
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    μ (arithmeticTupleCanonicalHull places tuple) ≤
      μ (arithmeticTupleIQHullUnitRegion places tuple) :=
  measure_mono (arithmeticTupleCanonicalHull_subset_IQHullUnitRegion places tuple)

/-- The signed real log-volume of the hull is at most that of the unit region. -/
theorem arithmeticTupleCanonicalHullHaarLog_le_unitRegionHaarLog
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    arithmeticTupleCanonicalHullHaarLog places tuple μ ≤
      arithmeticTupleIQHullUnitRegionHaarLog places tuple μ :=
  Real.log_le_log
    (arithmeticTupleCanonicalHull_measure_toReal_pos places tuple μ)
    (ENNReal.toReal_mono
      (arithmeticTupleIQHullUnitRegion_measure_ne_top places tuple μ)
      (arithmeticTupleCanonicalHull_measure_le_unitRegion places tuple μ))

/-- Under the normalization `mu unitRegion = 1`, the signed hull log-volume is
nonpositive. -/
theorem arithmeticTupleCanonicalHullHaarLog_nonpos_of_unitRegion_measure_one
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (hunit : μ (arithmeticTupleIQHullUnitRegion places tuple) = 1) :
    arithmeticTupleCanonicalHullHaarLog places tuple μ ≤ 0 := by
  have hle : μ (arithmeticTupleCanonicalHull places tuple) ≤ 1 := by
    simpa [hunit] using
      arithmeticTupleCanonicalHull_measure_le_unitRegion places tuple μ
  have hlog := Real.log_le_log
    (arithmeticTupleCanonicalHull_measure_toReal_pos places tuple μ)
    (by simpa using ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) hle)
  simpa [arithmeticTupleCanonicalHullHaarLog] using hlog

omit [Fintype ι] [BorelSpace (ArithmeticTensorTupleBlock places tuple)] in
/-- On a finite region, `haarLogVolume` is exactly `ofReal` of the signed real
logarithm. -/
theorem haarLogVolume_eq_ofReal_signedLog
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    {S : Set (ArithmeticTensorTupleBlock places tuple)} (hS : μ S < ⊤) :
    haarLogVolume μ S = ENNReal.ofReal (Real.log (μ S).toReal) :=
  haarLogVolume_of_lt_top hS

theorem arithmeticTupleCanonicalHull_haarLogVolume_eq_ofReal_signedLog
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    haarLogVolume μ (arithmeticTupleCanonicalHull places tuple) =
      ENNReal.ofReal (arithmeticTupleCanonicalHullHaarLog places tuple μ) :=
  haarLogVolume_of_lt_top
    (arithmeticTupleCanonicalHull_measure_lt_top_forSignedLog places tuple μ)

theorem arithmeticTupleIQHullUnitRegion_haarLogVolume_eq_ofReal_signedLog
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    haarLogVolume μ (arithmeticTupleIQHullUnitRegion places tuple) =
      ENNReal.ofReal (arithmeticTupleIQHullUnitRegionHaarLog places tuple μ) :=
  haarLogVolume_of_lt_top (arithmeticTupleIQHullUnitRegion_measure_lt_top places tuple μ)

end

end LeanFormal.IUT.NumberFieldFinitePlace
