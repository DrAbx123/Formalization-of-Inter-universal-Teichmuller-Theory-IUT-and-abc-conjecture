import tmp.sheaf.xif.paper.S2741ComparisonVolumeEqLogGenericActual

noncomputable section
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2742VolumeScalingGenericActual

open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2740HaarLogVolumeToRealActual
open LeanFormal.IUT.XiFPaper.S2741ComparisonVolumeEqLogGenericActual

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X)

theorem vol_scaling_of_haarLogVolume
    (vol vol' : ℝ) (S S' : Set X) (c : ℝ≥0)
    (hvol : vol = (haarLogVolume μ S).toReal)
    (hvol' : vol' = (haarLogVolume μ S').toReal)
    (hfinite : μ S ≠ ⊤) (hge1 : 1 ≤ (μ S).toReal)
    (hfinite' : μ S' ≠ ⊤) (hge1' : 1 ≤ (μ S').toReal)
    (hscale : μ S' = (c : ENNReal) * μ S) (hcpos : 0 < c) :
    vol' = vol + Real.log (c : ℝ) := by
  have hne : (μ S).toReal ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hge1)
  rw [hvol', hvol,
    haarLogVolume_toReal_eq_log μ S' hfinite' hge1',
    haarLogVolume_toReal_eq_log μ S hfinite hge1,
    hscale, ENNReal.toReal_mul, ENNReal.coe_toReal]
  rw [mul_comm ((c : ℝ)) ((μ S).toReal)]
  exact Real.log_mul hne (ne_of_gt hcpos)

#check vol_scaling_of_haarLogVolume
end LeanFormal.IUT.XiFPaper.S2742VolumeScalingGenericActual
end
