import tmp.sheaf.xif.paper.Mzk1P3LogMassRegionActual
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3HaarMassLogActual
open LeanFormal.IUT.XiFPaper.Mzk1P3LogMassRegionActual
variable {E : Type*} [MeasurableSpace E]
def haarLogMass (μ : Measure E) (S : Set E) : ℝ := regionLogMass μ S
theorem haarLogMass_eq (μ : Measure E) (S : Set E) :
    haarLogMass μ S = Real.log (μ S).toReal := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P3HaarMassLogActual
end