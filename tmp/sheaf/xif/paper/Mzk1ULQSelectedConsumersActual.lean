/- U-C: consumers of the selected q magnitude Q (route 6.2 Q_selected / audit).

Parameterized over the selected magnitude value QSel : R (david's
Mzk1ULQSelectedActual.QSelected once green) and the prime value lv; this file
records the consumption shape only: the M slot of C4/hP5 is Q/(2l) and stepVIII's
Q/M slot uses the same Q.  No inequality is claimed; when david's object lands its
value is fed in.
-/
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULQSelectedConsumersActual

/- the prime value l as a real number (caller passes (l.value : R)). -/
variable (lv : ℝ)

/-- the M slot associated with a q magnitude Q: M = Q/(2l). -/
noncomputable def MOfQ (Q : ℝ) : ℝ := Q / (2 * lv)

/-- PROVED (definitional): MOfQ is Q/(2l). -/
theorem MOfQ_eq (Q : ℝ) : MOfQ lv Q = Q / (2 * lv) := rfl

/-- the C4 Q/M slot relation: the M passed to hP5/hstepVIII is Q/(2l). -/
def HstepVIIIQM (Q M : ℝ) : Prop := M = MOfQ lv Q

/-- PROVED: an M satisfying the slot relation equals Q/(2l). -/
theorem HstepVIIIQM.elim {Q M : ℝ} (h : HstepVIIIQM lv Q M) : M = Q / (2 * lv) := h

/-- PROVED: given the slot relation, M is uniquely determined by Q. -/
theorem HstepVIIIQM.unique {Q M M' : ℝ} (h : HstepVIIIQM lv Q M)
    (h' : HstepVIIIQM lv Q M') : M = M' := by
  rw [h, h']

end LeanFormal.IUT.XiFPaper.Mzk1ULQSelectedConsumersActual
end
