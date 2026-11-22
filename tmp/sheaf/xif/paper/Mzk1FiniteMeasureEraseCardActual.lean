import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActual

/-! # Mzk1FiniteMeasureEraseCardActual — erase cardinality bound (real)

Real Lean (no sorry/axiom): the finite maximal count after erasing a point is bounded by the
original cardinality.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureEraseCardActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActual

attribute [local instance] Classical.decEq

universe u

theorem numMax_erase_le_card (S : Finset Qbar) (x : Qbar) :
    numMax (S.erase x) <= S.card := by
  have h1 : numMax (S.erase x) <= (S.erase x).card := numMax_le_card _
  have h2 : (S.erase x).card <= S.card := Finset.card_erase_le
  omega

def finiteMeasureEraseCardRows : List (String × String) :=
  [ ("numMax_erase_le_card", "PROVED") ]

theorem finiteMeasureEraseCardRows_length : finiteMeasureEraseCardRows.length = 1 := rfl

#check numMax_erase_le_card

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureEraseCardActual
end
