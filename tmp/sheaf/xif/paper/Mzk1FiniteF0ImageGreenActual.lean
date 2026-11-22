import tmp.sheaf.xif.paper.Mzk1FiniteMeasureImageActual
import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteF0ImageGreenActual — chain consumer over the green image-bound lemma

Real Lean (no sorry/axiom): f0 image degree bound obtained by chaining the PROVED
maxDeg_image_le (Mzk1FiniteMeasureImageActual, green) with degQ_aeval_le
(Mzk1NestedInductionActual, green).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageGreenActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImageActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_f0Image_le_green (S : Finset Qbar) (alpha0 : Qbar) :
    maxDeg (S.image (fun x => aeval x (minpoly ℚ alpha0))) <= maxDeg S := by
  apply maxDeg_image_le
  intro x hx
  have hxle : degQ x <= maxDeg S := by
    unfold maxDeg
    exact Finset.le_sup hx
  exact le_trans (degQ_aeval_le (minpoly ℚ alpha0) x) hxle

def finiteF0ImageGreenRows : List (String × String) :=
  [ ("maxDeg_f0Image_le_green", "PROVED (chain: image bound + aeval bound)") ]

theorem finiteF0ImageGreenRows_length : finiteF0ImageGreenRows.length = 1 := rfl

#check maxDeg_f0Image_le_green

end LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageGreenActual
end
