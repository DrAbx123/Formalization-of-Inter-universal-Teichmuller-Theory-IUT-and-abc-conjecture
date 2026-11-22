import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Analysis.SpecialFunctions.Log.Basic
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3MeasureTransportLogActual
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
/-- A measurable equivalence transports the measure of an image exactly. -/
theorem measure_map_image (μ : Measure X) (e : X ≃ᵐ Y) {S : Set X}
    (hS : MeasurableSet S) : (μ.map e) (e '' S) = μ S := by
  rw [Measure.map_apply e.measurable]
  · congr 1
    exact e.injective.preimage_image S
  · exact (MeasurableEquiv.measurableEmbedding e).measurableSet_image.mpr hS
/-- Log form of the exact transport: if two measures are related by a measurable
equivalence, their log-masses of corresponding images agree. -/
theorem log_measure_map_image (μ : Measure X) (e : X ≃ᵐ Y) {S : Set X}
    (hS : MeasurableSet S) :
    Real.log ((μ.map e) (e '' S)).toReal = Real.log (μ S).toReal := by
  rw [measure_map_image μ e hS]
end LeanFormal.IUT.XiFPaper.Mzk1P3MeasureTransportLogActual
end