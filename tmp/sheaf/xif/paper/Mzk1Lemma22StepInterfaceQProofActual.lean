import tmp.sheaf.xif.paper.Mzk1Lemma22StepInterfaceQActual
import tmp.sheaf.xif.paper.Mzk1Lemma22HypPreservationSeparationActual
import tmp.sheaf.xif.paper.Mzk1GChoiceUnramifiedActual
import tmp.sheaf.xif.paper.Mzk1GChoiceCardActual
import tmp.sheaf.xif.paper.Mzk1Lemma22ConditionedActual
import Mathlib.Tactic

/-! # Mzk1Lemma22StepInterfaceQProofActual — PROOF of the named step-interface existence

STEP 0 prior-art: consumes hull's green interface Mzk1Lemma22StepInterfaceQActual (structure +
named Prop step_interface_of_hypotheses_statement) and the green g-choice chain
(Mzk1GChoiceDataOfHypothesesActual, Mzk1GChoiceUnramifiedActual, Mzk1GChoiceCardActual,
Mzk1Lemma22ConditionedActual = hyp_preservation_full, Mzk1GChoiceScaleActual).  This file
supplies the existence proof (the named TODO), so bugfix #2 is discharged end-to-end:
phi = gPoly, targetS = Finset image, H-on-image, rational-point unramifiedness. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepInterfaceQProofActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceCardActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDataOfHypothesesActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceAvoidActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceDataActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationSeparationActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22ConditionedActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepInterfaceQActual

/-- Existence proof for the explicit step interface (discharges the named TODO). -/
theorem step_interface_of_hypotheses_proof :
    Mzk1Lemma22StepInterfaceQActual.step_interface_of_hypotheses_statement := by
  intro S β H hcard
  let D : Mzk1ScaleData := Mzk1ScaleData.ofHypotheses S β H hcard
  have hImage : Lemma22Hypotheses (S.image (polyMapPoints (gPoly D)))
      (polyMapPoints (gPoly D) β) :=
    hyp_preservation_full D H D.hn_even
  let P : Mzk1CardCollapseData :=
    { D := D
      h0S := H.1
      halpha2S := D.halpha2S
      halpha2_ne := D.halpha2_ne
      hlam := D.hlam_alpha2 }
  have hcardlt : (S.image (polyMapPoints (gPoly D))).card < S.card :=
    card_image_gPoly_lt P
  have hunr := gChoice_unramified D H
  let st : Mzk1Lemma22StepInterfaceQ :=
    { source := S
      beta := β
      g := gPoly D
      gdeg := gPoly_natDegree_pos D
      targetS := S.image (polyMapPoints (gPoly D))
      beta' := polyMapPoints (gPoly D) β
      targetS_eq := rfl
      beta'_eq := rfl
      card_lt := hcardlt
      hImage := hImage
      preserves := fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩
      unramified := by
        intro x hx
        have hmem : (polyMorphism (gPoly D) (gPoly_natDegree_pos D)).mapPoints
            (P1Point.ofFinite x) ∉
            (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ)) := by
          show polyMapPoints (gPoly D) (P1Point.ofFinite x) ∉
            (↑(S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ))
          exact hx
        have h := hunr (P1Point.ofFinite x) hmem
        simpa [polyUnramifiedAt, P1Point.ofFinite] using h }
  exact ⟨st, rfl, rfl, hcardlt⟩

#check step_interface_of_hypotheses_proof

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepInterfaceQProofActual
end
