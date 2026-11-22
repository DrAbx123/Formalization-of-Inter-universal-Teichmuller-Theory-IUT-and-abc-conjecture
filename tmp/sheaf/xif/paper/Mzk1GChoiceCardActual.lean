import tmp.sheaf.xif.paper.Mzk1GChoiceDegreeActual
import Mathlib.Tactic

/-! # Mzk1GChoiceCardActual — card collapse for the g-choice step (|image g| < |S|)

STEP 0 prior-art: corpus Lemma 2.2 lines 123-135 (the step decreases |S|); consumer layer
Mzk1Lemma22GChoiceConstructActual (gPoly/collapse) + Mzk1GChoiceDegreeActual (hdeg);
stepxi Mzk1GChoiceScaleActual provides the scale ordering/memberships (currently being
fixed); Mathlib Finset.card_image_iff / card_image_le reused.  No fake: the collision is
proved from g(0) = g(alpha2) with 0 and alpha2 distinct points of S. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceCardActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual

/-- Extra membership data for the card-collapse (supplied by the scale ordering layer). -/
structure Mzk1CardCollapseData where
  D : Mzk1ScaleData
  h0S : P1Point.ofFinite (0 : ℚ) ∈ D.S
  halpha2S : P1Point.ofFinite D.alpha2 ∈ D.S
  halpha2_ne : D.alpha2 ≠ 0
  hlam : D.lam * D.alpha2 = 1

/-- The image of S under g has strictly smaller cardinality: 0 and alpha2 collapse. -/
theorem card_image_gPoly_lt (P : Mzk1CardCollapseData) :
    (P.D.S.image (polyMapPoints (gPoly P.D))).card < P.D.S.card := by
  have hnotinj : ¬ Set.InjOn (polyMapPoints (gPoly P.D)) (↑P.D.S : Set (P1Point ℚ)) := by
    intro hinj
    have hdistinct : P1Point.ofFinite (0 : ℚ) ≠ P1Point.ofFinite P.D.alpha2 := by
      intro h
      have h0 : (0 : ℚ) = P.D.alpha2 := by
        simpa [P1Point.ofFinite] using h
      exact P.halpha2_ne h0.symm
    have hcollapse : (gPoly P.D).eval 0 = (gPoly P.D).eval P.D.alpha2 :=
      gPoly_collapse P.D P.hlam
    have heq : polyMapPoints (gPoly P.D) (P1Point.ofFinite (0 : ℚ)) =
        polyMapPoints (gPoly P.D) (P1Point.ofFinite P.D.alpha2) := by
      simpa [polyMapPoints, P1Point.ofFinite] using
        congrArg (fun v => (some v : P1Point ℚ)) hcollapse
    exact hdistinct (hinj P.h0S P.halpha2S heq)
  have hle : (P.D.S.image (polyMapPoints (gPoly P.D))).card ≤ P.D.S.card :=
    Finset.card_image_le
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact absurd (Finset.card_image_iff.mp heq) hnotinj

#check Mzk1CardCollapseData
#check card_image_gPoly_lt

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceCardActual
end
