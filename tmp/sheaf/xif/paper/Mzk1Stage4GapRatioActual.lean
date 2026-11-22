import tmp.sheaf.xif.paper.Mzk1Stage4ABCGapEstimatesActual

/-! # Mzk1Stage4GapRatioActual (stage4 lane; Gap1 full-ratio characterization)

A657 module (Gap1 full-ratio theorem): the Gap-1 comparison is characterized by the
FULL RATIO bound `height/regionVol ≤ 1` (and the ε-version `≤ 1+ε`), for positive
region volume.  This converts the additive gap into the paper ratio form without
changing any conclusion.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4GapRatioActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual

/-- Gap 1 gives the full ratio bound `height/regionVol ≤ 1`. -/
theorem gap1_ratio_le_one {height regionVol : Real} (h : Gap1 height regionVol)
    (hr : 0 < regionVol) : height / regionVol ≤ 1 := by
  rw [div_le_one hr]
  exact h.bound

/-- The ε-ratio characterization: `height ≤ (1+ε)·regionVol` iff
`height/regionVol ≤ 1+ε`. -/
theorem gap1_ratio_iff {height regionVol eps : Real} (hr : 0 < regionVol) :
    height ≤ (1 + eps) * regionVol ↔ height / regionVol ≤ 1 + eps := by
  rw [div_le_iff₀ hr]

/-- Gap 1 expressed through the ε-ratio structure. -/
theorem gap1_ratio_structure {height regionVol eps : Real} (hr : 0 < regionVol)
    (h : Gap1 height ((1 + eps) * regionVol)) :
    height / regionVol ≤ 1 + eps := by
  refine (gap1_ratio_iff hr).mp ?_
  exact h.bound

/-- The ratio normalization: `(height/regionVol)·regionVol = height`. -/
theorem ratio_mul {height regionVol : Real} (hr : regionVol ≠ 0) :
    height / regionVol * regionVol = height :=
  div_mul_cancel₀ height hr

#check gap1_ratio_le_one
#check gap1_ratio_iff
#check gap1_ratio_structure
#check ratio_mul

end LeanFormal.IUT.XiFPaper.Mzk1Stage4GapRatioActual
end
