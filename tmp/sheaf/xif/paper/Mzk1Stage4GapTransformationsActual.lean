import tmp.sheaf.xif.paper.Mzk1Stage4ABCGapEstimatesActual

/-! # Mzk1Stage4GapTransformationsActual (stage4 lane; gap transformations)

A652 module (real Gap1/Gap2 mathematical content): transformations that preserve the
two gap structures — positive scaling of both sides (Gap 1), factor/epsilon monotonicity
and additive-constant monotonicity (Gap 2), and the composed height-weight bound.
No conclusions are changed; all hypotheses remain explicit.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4GapTransformationsActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual

/-- Gap 1 is preserved by positive scaling of both sides. -/
theorem gap1_scale {height regionVol c : Real} (hc : 0 < c)
    (h : Gap1 height regionVol) : Gap1 (c * height) (c * regionVol) := by
  refine ⟨?_⟩
  exact mul_le_mul_of_nonneg_left h.bound (le_of_lt hc)

/-- Gap 2 is monotone in the epsilon: a larger epsilon keeps the bound. -/
theorem gap2_eps_mono {regionVol weight hull D eps eps' : Real}
    (h : Gap2 regionVol weight hull D eps) (heps : eps ≤ eps')
    (hweight : 0 ≤ weight) (hw1 : 0 ≤ 1 + eps) :
    Gap2 regionVol weight hull D eps' := by
  refine ⟨?_⟩
  have h1 : (1 + eps) * weight ≤ (1 + eps') * weight :=
    mul_le_mul_of_nonneg_right (by linarith) hweight
  linarith [h.bound]

/-- Gap 2 is monotone in the additive constant. -/
theorem gap2_D_mono {regionVol weight hull D D' eps : Real}
    (h : Gap2 regionVol weight hull D eps) (hDD : D ≤ D') :
    Gap2 regionVol weight hull D' eps := by
  refine ⟨by linarith [h.bound]⟩

/-- The composed bound: Gap 1 for `height`/`regionVol`, Gap 2 for `regionVol`, and
epsilon monotonicity give the height-weight bound at `eps`. -/
theorem gap1_gap2_height_weight {height regionVol weight hull D eps : Real}
    (h1 : Gap1 height regionVol) (h2 : Gap2 regionVol weight hull D eps) :
    height ≤ (1 + eps) * weight + (hull + D) :=
  le_trans h1.bound (by linarith [h2.bound])

#check gap1_scale
#check gap2_eps_mono
#check gap2_D_mono
#check gap1_gap2_height_weight

end LeanFormal.IUT.XiFPaper.Mzk1Stage4GapTransformationsActual
end
