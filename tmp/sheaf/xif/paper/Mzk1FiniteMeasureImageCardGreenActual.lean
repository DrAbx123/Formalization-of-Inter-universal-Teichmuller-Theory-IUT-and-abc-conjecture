import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteMeasureImageCardGreenActual — image cardinality/numMax consumer (real)

Real Lean (no sorry/axiom): the finite maximal count of an image is bounded by the source
cardinality (chain: filter-card bound + image-card bound).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImageCardGreenActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

theorem numMax_le_card_green (S : Finset Qbar) : numMax S <= S.card := by
  unfold numMax
  exact Finset.card_filter_le _ _

theorem numMax_image_le_card_green (S : Finset Qbar) (f : Qbar -> Qbar) :
    numMax (S.image f) <= S.card := by
  have h1 : numMax (S.image f) <= (S.image f).card := numMax_le_card_green _
  have h2 : (S.image f).card <= S.card := Finset.card_image_le
  omega

theorem card_image_le_green (S : Finset Qbar) (f : Qbar -> Qbar) :
    (S.image f).card <= S.card := Finset.card_image_le

def finiteMeasureImageCardGreenRows : List (String × String) :=
  [ ("numMax_image_le_card_green", "PROVED"), ("card_image_le_green", "PROVED") ]

theorem finiteMeasureImageCardGreenRows_length : finiteMeasureImageCardGreenRows.length = 2 := rfl

#check numMax_image_le_card_green

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureImageCardGreenActual
end
