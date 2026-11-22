import tmp.sheaf.xif.paper.Mzk1FiniteMeasureImage2Actual

/-! # Mzk1FiniteCritImageGreenActual — aeval-image degree bound chained over green lemmas

Real Lean (no sorry/axiom): the image of any finite set under x |-> aeval x (minpoly Q alpha0)
has maximal degree at most maxDeg S, chained from the PROVED
maxDeg_image_le_of_degQ_le (green) and degQ_aeval_le (green).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteCritImageGreenActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImage2Actual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_aevalImage_le_green (S : Finset Qbar) (alpha0 : Qbar) :
    maxDeg (S.image (fun x => aeval x (minpoly ℚ alpha0))) <= maxDeg S := by
  exact maxDeg_image_le_of_degQ_le S (fun x => aeval x (minpoly ℚ alpha0))
    (fun x => degQ_aeval_le (minpoly ℚ alpha0) x)

def finiteCritImageGreenRows : List (String × String) :=
  [ ("maxDeg_aevalImage_le_green", "PROVED (chain)") ]

theorem finiteCritImageGreenRows_length : finiteCritImageGreenRows.length = 1 := rfl

#check maxDeg_aevalImage_le_green

end LeanFormal.IUT.XiFPaper.Mzk1FiniteCritImageGreenActual
end
