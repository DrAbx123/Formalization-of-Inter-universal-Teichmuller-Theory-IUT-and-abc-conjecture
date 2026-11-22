import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4Gap2ConsumerActual (stage4 lane; unique filename)

A572 module: stage4-lane abstract consumer of the two IUT IV comparison gaps
(Gap 1 height vs region volume; Gap 2 region-volume estimate) producing the ABC
height-weight bound shape.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2ConsumerActual

/-- Gap 1 + Gap 2 give the ABC height-weight bound: from
`height <= regionVol` and `regionVol <= (1+eps)*weight + hull + D`, produce an
additive constant `A` with `height <= (1+eps)*weight + A`. -/
theorem height_bound_of_gaps {height regionVol weight eps hull D : Real}
    (hgap1 : height <= regionVol)
    (hgap2 : regionVol <= (1 + eps) * weight + hull + D) :
    ∃ A : Real, height <= (1 + eps) * weight + A :=
  ⟨hull + D, by linarith⟩

/-- The constant can be chosen nonnegative when the hull bound and residual are. -/
theorem height_bound_of_gaps_nonneg {height regionVol weight eps hull D : Real}
    (hgap1 : height <= regionVol)
    (hgap2 : regionVol <= (1 + eps) * weight + hull + D)
    (hhull : 0 <= hull) (hD : 0 <= D) :
    ∃ A : Real, 0 <= A ∧ height <= (1 + eps) * weight + A :=
  ⟨hull + D, by linarith, by linarith⟩

/-- The epsilon form: if the two gaps hold for every positive epsilon, then the
height bound holds with some constant depending on epsilon. -/
theorem height_bound_family {height : Real} {regionVol weight : Real → Real}
    {hull : Real → Real} {D : Real → Real}
    (hgap1 : ∀ eps, height <= regionVol eps)
    (hgap2 : ∀ eps, regionVol eps <= (1 + eps) * weight eps + hull eps + D eps) :
    ∀ eps : Real, ∃ A : Real, height <= (1 + eps) * weight eps + A :=
  fun eps => height_bound_of_gaps (hgap1 eps) (hgap2 eps)

#check height_bound_of_gaps
#check height_bound_of_gaps_nonneg
#check height_bound_family

end LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2ConsumerActual
end
