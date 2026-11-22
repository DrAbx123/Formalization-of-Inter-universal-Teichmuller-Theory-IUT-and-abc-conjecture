import tmp.sheaf.xif.paper.Mzk1P3NativeTensorLogComparisonActual
import Mathlib.MeasureTheory.Measure.Haar.Unique
/-! P3: log-mass scale factor between two additive Haar measures is exactly
the `addHaarScalarFactor` (the det/degree transport constant). -/
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3HaarScaleFactorLogActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NativeTensorLogComparisonActual
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [LocallyCompactSpace E] [MeasurableSpace E] [BorelSpace E]
/-- On an open set, two additive Haar measures differ by the additive Haar
scalar factor, hence their log masses differ by its log. -/
theorem logMass_eq_add_log_addHaarScalarFactor
    (ν μ : Measure E) [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    {s : Set E} (hs : IsOpen s)
    (hν0 : ν s ≠ 0) (hνtop : ν s ≠ ⊤)
    (hμ0 : μ s ≠ 0) (hμtop : μ s ≠ ⊤) :
    logMass ν s = logMass μ s +
      Real.log (Measure.addHaarScalarFactor ν μ : ℝ) := by
  have hsmul := Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen ν μ hs
  have hcpos_nn : 0 < Measure.addHaarScalarFactor ν μ :=
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ
  unfold logMass
  rw [hsmul]
  simp only [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
  rw [Real.log_mul]
  · ring
  · exact NNReal.coe_ne_zero.mpr hcpos_nn.ne'
  · exact (ENNReal.toReal_pos hμ0 hμtop).ne'
end LeanFormal.IUT.XiFPaper.Mzk1P3HaarScaleFactorLogActual
end