import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActual
import tmp.sheaf.xif.paper.Mzk1FiniteMeasureImageActual

/-! # Mzk1FiniteMeasureImageCardActual — image cardinality bounds (real)

Real Lean (no sorry/axiom): the finite maximal count of an image is bounded by the source
cardinality.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImageCardActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActual

attribute [local instance] Classical.decEq

universe u

theorem numMax_image_le_card (S : Finset Qbar) (f : Qbar -> Qbar) :
    numMax (S.image f) <= S.card := by
  have h1 : numMax (S.image f) <= (S.image f).card := numMax_le_card _
  have h2 : (S.image f).card <= S.card := Finset.card_image_le
  omega

def finiteMeasureImageCardRows : List (String × String) :=
  [ ("numMax_image_le_card", "PROVED") ]

theorem finiteMeasureImageCardRows_length : finiteMeasureImageCardRows.length = 1 := rfl

#check numMax_image_le_card

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImageCardActual
end
