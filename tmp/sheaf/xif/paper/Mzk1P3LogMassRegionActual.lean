import tmp.sheaf.xif.paper.Mzk1P3MassIdentificationActual
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3LogMassRegionActual
variable {E : Type*} [MeasurableSpace E]
def regionLogMass (μ : Measure E) (S : Set E) : ℝ := Real.log (μ S).toReal
theorem regionLogMass_mul (μ : Measure E) (S T : Set E)
    (hS : μ S ≠ 0) (hSfin : μ S ≠ ⊤) (hT : μ T ≠ 0) (hTfin : μ T ≠ ⊤) :
    regionLogMass μ S + regionLogMass μ T = Real.log ((μ S).toReal * (μ T).toReal) := by
  unfold regionLogMass
  rw [Real.log_mul]
  · exact (ENNReal.toReal_pos hS hSfin).ne'
  · exact (ENNReal.toReal_pos hT hTfin).ne'
end LeanFormal.IUT.XiFPaper.Mzk1P3LogMassRegionActual
end