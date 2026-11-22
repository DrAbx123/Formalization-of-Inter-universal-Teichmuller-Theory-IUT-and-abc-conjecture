import tmp.sheaf.xif.paper.Mzk1FiniteF0ImageBoundActualAdapted
import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActualAdapted

/-! # Mzk1FiniteF0ImageCardActualAdapted — f0 image count bound (real)

Real Lean (no sorry/axiom): the finite maximal count of the f0 image is bounded by the source
cardinality (cardinality of an image never grows).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageCardActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActualAdapted
open LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageBoundActualAdapted

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

end LeanFormal.IUT.XiFPaper.Mzk1FiniteF0ImageCardActualAdapted
end
