import tmp.sheaf.xif.paper.S2740HaarLogVolumeToRealActual

noncomputable section
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2741ComparisonVolumeEqLogGenericActual

open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2740HaarLogVolumeToRealActual

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X)

theorem vol_eq_log_of_haarLogVolume_toReal
    (vol : ℝ) (S : Set X)
    (hvol : vol = (haarLogVolume μ S).toReal)
    (hfinite : μ S ≠ ⊤) (hge1 : 1 ≤ (μ S).toReal) :
    vol = Real.log ((μ S).toReal) := by
  rw [hvol, haarLogVolume_toReal_eq_log μ S hfinite hge1]

#check vol_eq_log_of_haarLogVolume_toReal
end LeanFormal.IUT.XiFPaper.S2741ComparisonVolumeEqLogGenericActual
end
