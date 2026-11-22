import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteStepSetCardActual — cardinality bound for the finite step set (real)

Real Lean (no sorry/axiom): the step set is contained in two images, so its cardinality is
bounded by the union/image cardinality estimates.  Registry frozen 14041. -/

open Polynomial

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetCardActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

theorem card_stepSet_le (S : Finset Qbar) (alpha0 : Qbar) :
    (stepSet S alpha0).card <= (S.card + (conjSet alpha0).card) + (critSet alpha0).card := by
  unfold stepSet
  have h1 : (((S ∪ conjSet alpha0).image (fun a => aeval a (minpoly ℚ alpha0))) ∪
      (critSet alpha0).image (fun xi => aeval xi (minpoly ℚ alpha0))).card
      <= ((S ∪ conjSet alpha0).image (fun a => aeval a (minpoly ℚ alpha0))).card +
        ((critSet alpha0).image (fun xi => aeval xi (minpoly ℚ alpha0))).card :=
    Finset.card_union_le _ _
  have h2 : ((S ∪ conjSet alpha0).image (fun a => aeval a (minpoly ℚ alpha0))).card
      <= (S ∪ conjSet alpha0).card := Finset.card_image_le
  have h3 : ((critSet alpha0).image (fun xi => aeval xi (minpoly ℚ alpha0))).card
      <= (critSet alpha0).card := Finset.card_image_le
  have h4 : (S ∪ conjSet alpha0).card <= S.card + (conjSet alpha0).card :=
    Finset.card_union_le _ _
  omega

def finiteStepSetCardRows : List (String × String) :=
  [ ("card_stepSet_le", "PROVED (union/image cardinality)") ]

theorem finiteStepSetCardRows_length : finiteStepSetCardRows.length = 1 := rfl

#check card_stepSet_le

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetCardActual
end
