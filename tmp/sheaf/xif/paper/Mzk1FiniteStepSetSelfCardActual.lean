import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteStepSetSelfCardActual — self-contained step-set cardinality bound (real)

Real Lean (no sorry/axiom): cardinality bound for the paper's step set, self-contained
(depends only on the green Mzk1NestedInductionActual).  Registry frozen 14041. -/

open Polynomial

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetSelfCardActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

theorem card_stepSet_le' (S : Finset Qbar) (alpha0 : Qbar) :
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

def finiteStepSetSelfCardRows : List (String × String) :=
  [ ("card_stepSet_le'", "PROVED (self-contained)") ]

theorem finiteStepSetSelfCardRows_length : finiteStepSetSelfCardRows.length = 1 := rfl

theorem card_f0Image_le (S : Finset Qbar) (alpha0 : Qbar) :
    (S.image (fun x => aeval x (minpoly ℚ alpha0))).card <= S.card :=
  Finset.card_image_le

theorem card_critImage_le (alpha0 : Qbar) :
    ((critSet alpha0).image (fun x => aeval x (minpoly ℚ alpha0))).card
      <= (critSet alpha0).card :=
  Finset.card_image_le

#check card_f0Image_le

#check card_stepSet_le'

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetSelfCardActual
end
