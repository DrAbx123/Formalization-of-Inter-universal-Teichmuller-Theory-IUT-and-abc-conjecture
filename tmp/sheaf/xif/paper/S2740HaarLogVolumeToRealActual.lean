import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

noncomputable section
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2740HaarLogVolumeToRealActual

open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X)

theorem haarLogVolume_toReal_eq_log
    (S : Set X) (hfinite : μ S ≠ ⊤) (hge1 : 1 ≤ (μ S).toReal) :
    (haarLogVolume μ S).toReal = Real.log ((μ S).toReal) := by
  rw [haarLogVolume_of_lt_top (lt_top_iff_ne_top.mpr hfinite)]
  rw [ENNReal.toReal_ofReal (Real.log_nonneg hge1)]

#check haarLogVolume_toReal_eq_log
end LeanFormal.IUT.XiFPaper.S2740HaarLogVolumeToRealActual
end
