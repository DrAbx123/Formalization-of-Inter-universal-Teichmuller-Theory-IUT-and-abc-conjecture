import tmp.sheaf.xif.paper.Mzk1FiniteMeasureImage2Actual

/-! # Mzk1FiniteF0ImageBoundActual — f0 image degree bound (real, reuse of degQ_aeval_le)

Real Lean (no sorry/axiom): the image of a finite set under x |-> aeval x (minpoly Q alpha0)
(the paper's f0 step) does not increase the finite maximal degree, by the PROVED degree bound
degQ_aeval_le.  This is a genuine f4 ingredient bridging the f0 geometry and the measure.
Registry frozen 14041. -/

open Polynomial

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageBoundActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImage2Actual

attribute [local instance] Classical.decEq

universe u

/-- f0 = minpoly step does not increase the finite maximal degree. -/
theorem maxDeg_f0Image_le (S : Finset Qbar) (alpha0 : Qbar) :
    maxDeg (S.image (fun x => aeval x (minpoly ℚ alpha0))) <= maxDeg S := by
  exact maxDeg_image_le_of_degQ_le S (fun x => aeval x (minpoly ℚ alpha0))
    (fun x => degQ_aeval_le (minpoly ℚ alpha0) x)

/-- f0 critical-value image has strictly smaller degree than the base point (PROVED bound). -/
theorem degQ_f0Image_lt_of_critical (alpha0 x : Qbar)
    (hx : aeval x (derivative (minpoly ℚ alpha0)) = 0) :
    degQ (aeval x (minpoly ℚ alpha0)) < degQ alpha0 :=
  degQ_critValue_lt alpha0 x hx

def finiteF0ImageBoundRows : List (String × String) :=
  [ ("maxDeg_f0Image_le", "PROVED (degQ_aeval_le)"),
    ("degQ_f0Image_lt_of_critical", "PROVED (degQ_critValue_lt)") ]

theorem finiteF0ImageBoundRows_length : finiteF0ImageBoundRows.length = 2 := rfl

#check maxDeg_f0Image_le

end LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageBoundActual
end
