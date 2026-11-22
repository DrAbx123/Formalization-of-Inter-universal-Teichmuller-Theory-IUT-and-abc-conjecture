import tmp.sheaf.xif.paper.Mzk1Stage4GapTransformationsActual

/-! # Mzk1Stage4GapWeightCounterexampleActual (stage4 lane; weight counterexample)

A652 module (real Gap mathematical content): the epsilon-monotonicity of Gap 2 GENUINELY
requires a nonnegative weight — a concrete counterexample with negative weight shows the
bound at `eps` can fail at a larger `eps'`.  This justifies the hypotheses of
`gap2_eps_mono` and is not a shortcut.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4GapWeightCounterexampleActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual

/-- Counterexample: with negative weight, Gap 2 at `eps = 0` does NOT imply Gap 2 at
`eps' = 1`. -/
theorem gap2_eps_mono_fails_with_negative_weight :
    ∃ regionVol weight hull D eps eps' : Real,
      Gap2 regionVol weight hull D eps ∧ ¬ Gap2 regionVol weight hull D eps' := by
  refine ⟨-1, -1, 0, 0, 0, 1, ⟨by norm_num⟩, ?_⟩
  intro h
  have hb := h.bound
  norm_num at hb

/-- The counterexample's data, explicitly: `regionVol = weight = -1`, `hull = D = 0`,
`eps = 0`, `eps' = 1`. -/
theorem gap2_counterexample_data :
    Gap2 (-1) (-1) 0 0 0 ∧ ¬ Gap2 (-1) (-1) 0 0 1 := by
  refine ⟨⟨by norm_num⟩, ?_⟩
  intro h
  have hb := h.bound
  norm_num at hb

#check gap2_eps_mono_fails_with_negative_weight
#check gap2_counterexample_data

end LeanFormal.IUT.XiFPaper.Mzk1Stage4GapWeightCounterexampleActual
end
