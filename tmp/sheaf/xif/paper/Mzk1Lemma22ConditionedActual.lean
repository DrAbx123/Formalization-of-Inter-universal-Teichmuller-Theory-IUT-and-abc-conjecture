import tmp.sheaf.xif.paper.Mzk1GChoiceDataOfHypothesesActual
import tmp.sheaf.xif.paper.Mzk1Lemma22HypPreservationActual
import tmp.sheaf.xif.paper.Mzk1Lemma22HypPreservationSeparationActual
import tmp.sheaf.xif.paper.Mzk1GChoiceIntegrationActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22ConditionedActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceAvoidActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationSeparationActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22StatementShapeActual

theorem hyp_preservation_full (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta)
    (hne : Even D.n) :
    Lemma22Hypotheses (D.S.image (polyMapPoints (gPoly D)))
      (polyMapPoints (gPoly D) D.beta) :=
  ⟨target_zero_mem D H hne, target_infty_mem D H,
   target_positivity D H hne, target_beta_notin D H, hyp_separation D H hne⟩

theorem hyp_preservation_of_hypotheses (S : Finset (P1Point ℚ)) (β : P1Point ℚ)
    (H : Lemma22Hypotheses S β) (hcard : 3 < S.card) :
    Lemma22Hypotheses
      ((Mzk1ScaleData.ofHypotheses S β H hcard).S.image
        (polyMapPoints (gPoly (Mzk1ScaleData.ofHypotheses S β H hcard))))
      (polyMapPoints (gPoly (Mzk1ScaleData.ofHypotheses S β H hcard))
        (Mzk1ScaleData.ofHypotheses S β H hcard).beta) :=
  hyp_preservation_full (Mzk1ScaleData.ofHypotheses S β H hcard) H
    (Mzk1ScaleData.ofHypotheses S β H hcard).hn_even


end LeanFormal.IUT.XiFPaper.Mzk1Lemma22ConditionedActual
end

