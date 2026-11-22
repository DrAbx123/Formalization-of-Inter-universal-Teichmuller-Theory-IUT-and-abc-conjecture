import tmp.sheaf.xif.paper.Mzk1FiniteF0ImageBoundActual
import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActual

/-! # Mzk1FiniteF0ImageCardActual — f0 image count bound (real)

Real Lean (no sorry/axiom): the finite maximal count of the f0 image is bounded by the source
cardinality (cardinality of an image never grows).  Registry frozen 14041. -/

open Polynomial

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageCardActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageBoundActual

universe u

theorem numMax_f0Image_le_card (S : Finset Qbar) (alpha0 : Qbar) :
    numMax (S.image (fun x => aeval x (minpoly ℚ alpha0))) <= S.card := by
  have h1 : numMax (S.image (fun x => aeval x (minpoly ℚ alpha0)))
      <= (S.image (fun x => aeval x (minpoly ℚ alpha0))).card := numMax_le_card _
  have h2 : (S.image (fun x => aeval x (minpoly ℚ alpha0))).card <= S.card :=
    Finset.card_image_le
  omega

def finiteF0ImageCardRows : List (String × String) :=
  [ ("numMax_f0Image_le_card", "PROVED") ]

theorem finiteF0ImageCardRows_length : finiteF0ImageCardRows.length = 1 := rfl

#check numMax_f0Image_le_card

end LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageCardActual
end
