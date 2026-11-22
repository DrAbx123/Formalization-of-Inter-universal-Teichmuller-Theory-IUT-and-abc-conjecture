import tmp.sheaf.xif.paper.Mzk1P3HaarScaleFactorLogActual
/-! #10 det-Haar consumer: the measure-scale factor is the standard additive
Haar scalar factor, so the log-volume transport is exact and positive. -/
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3DetHaarScaleConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1P3HaarScaleFactorLogActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NativeTensorLogComparisonActual
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [LocallyCompactSpace E] [MeasurableSpace E] [BorelSpace E]
theorem detHaar_scale_factor_pos
    (ν μ : Measure E) [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν] :
    0 < (Measure.addHaarScalarFactor ν μ : ℝ) := by
  exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ
/-- det-Haar measure-scale readout: the log-mass ratio is the log of the
additive Haar scalar factor on every open set. -/
theorem detHaar_logMass_ratio
    (ν μ : Measure E) [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    {s : Set E} (hs : IsOpen s)
    (hν0 : ν s ≠ 0) (hνtop : ν s ≠ ⊤)
    (hμ0 : μ s ≠ 0) (hμtop : μ s ≠ ⊤) :
    logMass ν s - logMass μ s =
      Real.log (Measure.addHaarScalarFactor ν μ : ℝ) := by
  rw [logMass_eq_add_log_addHaarScalarFactor ν μ hs hν0 hνtop hμ0 hμtop]
  ring
end LeanFormal.IUT.XiFPaper.Mzk1P3DetHaarScaleConsumerActual
end