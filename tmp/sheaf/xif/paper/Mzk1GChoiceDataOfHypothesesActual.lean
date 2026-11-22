import tmp.sheaf.xif.paper.Mzk1GChoiceUnramifiedActual
import tmp.sheaf.xif.paper.Mzk1GChoiceCardActual
import tmp.sheaf.xif.paper.Mzk1GChoiceIntegrationActual
import tmp.sheaf.xif.paper.Mzk1Lemma22GChoiceDataActual
import tmp.sheaf.xif.paper.Mzk1Lemma22CompositionActual
import tmp.sheaf.xif.paper.Mzk1Lemma22InductionActual
import tmp.sheaf.xif.paper.Mzk1GChoiceDegreeActual
import Mathlib.Tactic

/-! # Mzk1GChoiceDataOfHypothesesActual — assemble Mzk1GChoiceData + stepExists for Lemma 2.2

STEP 0 prior-art: resume priority (Lead).  Reuse (all GREEN/CITABLE): Mzk1GChoiceAvoidActual
(gChoice_avoids), Mzk1GChoiceUnramifiedActual (gChoice_unramified), Mzk1GChoiceCardActual
(card_image_gPoly_lt), Mzk1GChoiceDegreeActual (hdeg), Mzk1GChoiceIntegrationActual
(ofHypotheses), Mzk1GChoiceScaleActual (scale package).  This file assembles the four
g-choice fields and the stepExists shape consumed by the partial induction. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceDataOfHypothesesActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceCardActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceAvoidActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceDataActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22CompositionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22InductionActual

/-- Assemble the g-choice data from Lemma22Hypotheses + cardinality bound. -/
noncomputable def gChoiceData_of_hypotheses
    (S : Finset (P1Point ℚ)) (β : P1Point ℚ)
    (H : Lemma22Hypotheses S β) (hcard : 3 < S.card) : Mzk1GChoiceData :=
  let D : Mzk1ScaleData := Mzk1ScaleData.ofHypotheses S β H hcard
  let P : Mzk1CardCollapseData :=
    { D := D
      h0S := H.1
      halpha2S := D.halpha2S
      halpha2_ne := D.halpha2_ne
      hlam := D.hlam_alpha2 }
  { S := D.S
    beta := D.beta
    g := gPoly D
    hdeg := gPoly_natDegree_pos D
    hcard := card_image_gPoly_lt P
    havoids := gChoice_avoids D H
    hunram := gChoice_unramified D H }

/-- The stepExists shape consumed by mzk1Lemma22_partial_induction, conditioned on
Lemma22Hypotheses. -/
theorem stepExists_of_hypotheses (S : Finset (P1Point ℚ)) (β : P1Point ℚ)
    (H : Lemma22Hypotheses S β) (hcard : 3 < S.card) :
    ∃ st : Mzk1Lemma22InductionStep ℚ,
      st.source = S ∧ st.beta = β ∧
      st.targetSet = (↑st.targetS : Set (P1Point ℚ)) :=
  let data := gChoiceData_of_hypotheses S β H hcard
  ⟨gChoiceStep data, rfl, rfl, rfl⟩

#check gChoiceData_of_hypotheses
#check stepExists_of_hypotheses

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceDataOfHypothesesActual
end
