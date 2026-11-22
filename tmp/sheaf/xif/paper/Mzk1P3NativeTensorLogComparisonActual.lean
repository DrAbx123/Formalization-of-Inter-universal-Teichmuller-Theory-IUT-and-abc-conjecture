import tmp.sheaf.xif.paper.Mzk1P3ProductHaarPiActual
import tmp.sheaf.xif.paper.Mzk1P0NativeTensorConsumerActual
/-! P3: comparison interface between native tensor log-volume and product
log-volume via an explicit measure scale factor.  The carrier/det
identification is the named missing bridge `p2NativeProductBlockMissing`. -/
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3NativeTensorLogComparisonActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
/-- Log of a finite measure mass. -/
def logMass {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : Set α) : ℝ :=
  Real.log (μ S).toReal
/-- A positive real scale factor contributes exactly its log to the mass. -/
theorem logMass_eq_add_log_factor
    {α : Type*} [MeasurableSpace α]
    (ν μ : Measure α) (S : Set α) (c : ℝ)
    (hc : 0 < c) (hν0 : ν S ≠ 0) (hνtop : ν S ≠ ⊤)
    (hμ0 : μ S ≠ 0) (hμtop : μ S ≠ ⊤)
    (h : (ν S).toReal = c * (μ S).toReal) :
    logMass ν S = Real.log c + logMass μ S := by
  unfold logMass
  rw [h, Real.log_mul hc.ne' (ENNReal.toReal_pos hμ0 hμtop).ne']

end LeanFormal.IUT.XiFPaper.Mzk1P3NativeTensorLogComparisonActual
end