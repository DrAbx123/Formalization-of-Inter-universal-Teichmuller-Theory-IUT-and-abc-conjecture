import tmp.sheaf.xif.paper.Mzk1FiniteMeasureImageActual

/-! # Mzk1FiniteMeasureImage2Actual — degree-dominated image bound (real)

Real Lean (no sorry/axiom): if a map does not increase degrees pointwise, it does not increase
the finite maximal degree of a finite set.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImage2Actual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImageActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_image_le_of_degQ_le (S : Finset Qbar) (f : Qbar -> Qbar)
    (h : forall x, degQ (f x) <= degQ x) :
    maxDeg (S.image f) <= maxDeg S := by
  apply maxDeg_image_le
  intro x hx
  have hxle : degQ x <= maxDeg S := by
    unfold maxDeg
    exact Finset.le_sup hx
  exact le_trans (h x) hxle

def finiteMeasureImage2Rows : List (String × String) :=
  [ ("maxDeg_image_le_of_degQ_le", "PROVED") ]

theorem finiteMeasureImage2Rows_length : finiteMeasureImage2Rows.length = 1 := rfl

#check maxDeg_image_le_of_degQ_le

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImage2Actual
end
