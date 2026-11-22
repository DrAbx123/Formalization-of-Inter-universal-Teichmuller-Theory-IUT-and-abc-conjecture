import tmp.sheaf.xif.paper.Mzk1Gap1ScalingLawTargetActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4BadInvScaleBlockingActual (stage4 lane; badInvScale blocking analysis)

A660 module: blocking analysis for the hull `badInvScale` product law (hull lane file
`Mzk1ScalingDirectionActual`, READ-level citation only: it is still being written, so
this file does NOT import it).  Recorded facts from its listed target:
* local factors are inverse prime-power Haar factors (1D lemma `prime_inv_smul_measure`,
  `prime_pow_inv_smul_measure`);
* the product log-volume increases by the bad-support weighted sum `Σ e_b d_b log p_b`,
  which equals `log N` ONLY when every prime of `N` is bad and `d_b = 1` (explicit
  hypothesis `hcop` for the bad-part);
* hence the scaling-law ratio is the bad part, not the full `N`, in general — this is
  the key blocking item for Gap 1 in the unfavourable case.
Elementary consequences are proved here; no object or conclusion is changed.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4BadInvScaleBlockingActual

/-- A ratio at most 1 has nonpositive logarithm (the bad-part ratio can be `< 1`). -/
theorem log_nonpos_of_ratio_le_one {r : Real} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    Real.log r ≤ 0 := by
  have h1 : Real.log r ≤ Real.log 1 := Real.log_le_log hr0 hr1
  simpa using h1

/-- The arithmetic condition is nontrivial: if the available right-hand side is 0, the
condition `log c ≤ (1+ε)·0` already fails for `c = 2` (since `log 2 > 0`). -/
theorem arithmetic_condition_nontrivial :
    ¬ (Real.log (2 : Real) ≤ (1 + 1 / 10) * (0 + 0 + 0)) := by
  have h : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  intro hle
  nlinarith

/-- The bad-part ratio (`< 1`) is the unfavourable direction for the arithmetic
condition: comparing with ratio 1 gives a genuinely weaker bound. -/
theorem badpart_ratio_unfavourable {unit const ratio : Real}
    (hunit : 0 ≤ unit) (hconst : 0 ≤ const)
    (hr0 : 0 < ratio) (hr1 : ratio ≤ 1) :
    Real.log ratio ≤ 0 ∧ unit + const + Real.log ratio ≤ unit + const := by
  refine ⟨log_nonpos_of_ratio_le_one hr0 hr1, ?_⟩
  linarith [log_nonpos_of_ratio_le_one hr0 hr1]

/-- The blocking-status record. -/
def badInvScaleBlockingRows : List (String × String) :=
  [ ("hull source", "Mzk1ScalingDirectionActual (badInvScale measure/product log laws; still being written)")
  , ("direction", "inverse scaling by N increases volumes by Σ_b e_b d_b log p_b (hull docstring)")
  , ("full-N condition", "equals log N only if every prime of N is bad and d_b = 1")
  , ("key blocking", "bad-part ratio < full N in general -> Gap 1 arithmetic condition weaker")
  , ("favourable case", "full-ratio scaling law suffices (gap1_of_fullRatio in target file)")
  ]

/-- The blocking record has five rows. -/
theorem badInvScaleBlockingRows_length : badInvScaleBlockingRows.length = 5 := rfl

#check log_nonpos_of_ratio_le_one
#check arithmetic_condition_nontrivial
#check badpart_ratio_unfavourable
#check badInvScaleBlockingRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4BadInvScaleBlockingActual
end
