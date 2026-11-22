import Mathlib.Tactic

/-! # Gap1/Gap2 real mathematical calibration (non-vacuity/content) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GapCalibrationShaActual

/-- Gap 2 cannot be made uniform in `D = 0`: there are volumes/weights/theta with
`regionVolume > weight + theta + 0`. -/
theorem gap2_zeroD_counterexample :
    ¬ (forall (regionVolume weight theta : Real),
      regionVolume ≤ (1 + (0 : Real)) * weight + theta + 0) := by
  intro h
  have h1 := h 1 0 0
  norm_num at h1

/-- The `(1 + ε)` slack is genuinely needed for Gap 1 at positive ε: there are
`h, L` with `L < h` yet `h ≤ (1 + ε) * L` for ε = 1. -/
theorem gap1_slack_witness :
    exists h L : Real, L < h ∧ h ≤ (1 + (1 : Real)) * L := by
  refine ⟨(3 / 2 : Real), (1 : Real), ?_⟩
  constructor <;> norm_num

#print axioms gap2_zeroD_counterexample
#print axioms gap1_slack_witness

end LeanFormal.IUT.XiFPaper.Mzk1GapCalibrationShaActual
