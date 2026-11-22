import tmp.sheaf.xif.paper.Mzk1P3TensorCoreScalingActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3CoreScalingExplicitActual
/-- Explicit scalar form of the conditional core scaling constant. -/
def coreScalingConstant (c : ENNReal) : ENNReal := c
theorem coreScaling_mul (c : ENNReal) (m : ENNReal) :
    coreScalingConstant c * m = c * m := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P3CoreScalingExplicitActual
end