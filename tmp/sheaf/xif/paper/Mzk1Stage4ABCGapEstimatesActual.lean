import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4ABCGapEstimatesActual (stage4 lane; unique filename)

A590 module: stage4-lane formalization of the two IUT IV comparison gaps used by the
ABC height-region input, with a numeric witness in the 11a1@l=13 data:
* Gap 1: height <= region volume;
* Gap 2: region volume <= (1+eps) weight + hull + D;
* combined bound and its numeric instance.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual

/-- Gap 1 (height vs region volume). -/
structure Gap1 (height regionVol : Real) : Prop where
  bound : height <= regionVol

/-- Gap 2 (region-volume estimate). -/
structure Gap2 (regionVol weight hull D eps : Real) : Prop where
  bound : regionVol <= (1 + eps) * weight + hull + D

/-- Combined estimate: the two gaps give a height bound with additive constant. -/
theorem combined (height regionVol weight hull D eps : Real)
    (h1 : Gap1 height regionVol)
    (h2 : Gap2 regionVol weight hull D eps) :
    height <= (1 + eps) * weight + (hull + D) :=
  by
  have h1b : height <= regionVol := h1.bound
  have h2b : regionVol <= (1 + eps) * weight + hull + D := h2.bound
  linarith

/-- Combined estimate in existential-constant form. -/
theorem combined_exists (height regionVol weight hull D eps : Real)
    (h1 : Gap1 height regionVol)
    (h2 : Gap2 regionVol weight hull D eps) :
    ∃ A : Real, height <= (1 + eps) * weight + A :=
  ⟨hull + D, combined height regionVol weight hull D eps h1 h2⟩

/-- Numeric Gap 1: `log 11 <= 2 log 11`. -/
theorem gap1_numeric : Gap1 (Real.log 11) (2 * Real.log 11) where
  bound := by
    have h : (0 : Real) < Real.log 11 :=
      Real.log_pos (by norm_num)
    linarith

/-- Numeric Gap 2: `2 log 11 <= (1 + 1/10) log 11 + 11 + 0`. -/
theorem gap2_numeric : Gap2 (2 * Real.log 11) (Real.log 11) 11 0 (1 / 10) where
  bound := by
    have h : Real.log 11 < 11 := by
      have := Real.log_le_sub_one_of_pos (show (0 : Real) < 11 by norm_num)
      linarith
    nlinarith

/-- Numeric combined estimate with the two gaps. -/
theorem combined_numeric :
    ∃ A : Real, Real.log 11 <= (1 + 1 / 10) * Real.log 11 + A :=
  combined_exists (Real.log 11) (2 * Real.log 11) (Real.log 11) 11 0 (1 / 10)
    gap1_numeric gap2_numeric

#check Gap1
#check Gap2
#check combined
#check combined_exists
#check gap1_numeric
#check gap2_numeric
#check combined_numeric

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual
end
