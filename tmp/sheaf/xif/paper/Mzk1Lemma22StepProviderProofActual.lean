import tmp.sheaf.xif.paper.Mzk1Lemma22InductionProofActual
import tmp.sheaf.xif.paper.Mzk1Lemma22CritValueActual
import tmp.sheaf.xif.paper.Mzk1Lemma22StepInterfaceQProofActual
import tmp.sheaf.xif.paper.Mzk1GChoiceCardActual
import tmp.sheaf.xif.paper.Mzk1Lemma22ConditionedActual
import tmp.sheaf.xif.paper.Mzk1CritValueInImageProofActual
import Mathlib.Tactic

/-! # Mzk1Lemma22StepProviderProofActual — discharges StepProviderStatement (F=Q component)

STEP 0 prior-art: reuse Mzk1Lemma22InductionProofActual (StepProviderStatement def),
Mzk1Lemma22CritValueActual (critValueInImage_proof PROVED), Mzk1Lemma22StepInterfaceQProofActual
(step interface + existence), Mzk1GChoiceCardActual, Mzk1Lemma22ConditionedActual,
Mzk1GChoiceScaleActual/UnramifiedActual.  Constructs the explicit step st = gPoly D and its
C-point CV-in-image property, so the named step provider of the conditional induction is
PROVED for the rational scope.  BaseProviderStatement remains a NAMED input.

INTEGRITY NOTE (Lead A356; 谢德 re-audit): the proven chain uses the UNCHANGED stepxi
Good (C-point condition: aeval z f ∉ {0,1} -> aeval z f.derivative ≠ 0).  The unnormalized gPoly
does NOT satisfy the literal 0/1 critical-value statement (refuted in Mzk1CritValueInImageProofActual);
intermediate steps use the IMAGE-BASED CritValueInImageStatement, and the composite's C-point
condition is derived via the two chain-rule cases.  Base f = C c * X satisfies it vacuously
(derivative = C c ≠ 0).  Mzk1BaseProviderProofActual (sorryAx) is NOT used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepProviderProofActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceCardActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceAvoidActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDataOfHypothesesActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceDataActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationSeparationActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22ConditionedActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepInterfaceQActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22CritValueActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22InductionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1CritValueInImageProofActual

/-- The named step provider of the conditional induction is PROVED (rational scope). -/
theorem stepProvider_holds : StepProviderStatement := by
  intro S β hbig H
  let D : Mzk1ScaleData := Mzk1ScaleData.ofHypotheses S β H hbig
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
  refine ⟨st, rfl, rfl, hcardlt, ?_⟩
  intro z hz
  obtain ⟨p, hpS, v, hv, hgpv⟩ := critValueInImageStatement_proved D H z hz
  exact ⟨p, hpS, v, hv, hgpv⟩

theorem mzk1Lemma22_induction_of_base (hbase : BaseProviderStatement) :
    Mzk1Lemma22InductionStatement :=
  mzk1Lemma22_induction_conditional hbase stepProvider_holds

theorem mzk1Lemma22_target_of_base (hbase : BaseProviderStatement)
    (S : Finset (P1Point ℚ)) (β : P1Point ℚ) (H : Lemma22Hypotheses S β) :
    Mzk1Lemma22Target S β :=
  target_of_induction (mzk1Lemma22_induction_of_base hbase) S β H

def stepProviderRows : List (String × String × String) :=
  [ ("step provider existence (rational)", "PROVED", "stepProvider_holds (gPoly D, card collapse, H-on-image)")
  , ("C-point CV-in-image (image-based)", "PROVED", "Mzk1CritValueInImageProofActual.critValueInImageStatement_proved")
  , ("literal 0/1 critical-value statement", "REFUTED", "s3135_critValueInImage_refuted (unnormalized gPoly; correct 0/1 only after Belyi normalization)")
  , ("conditional induction -> target (only base named)", "PROVED CONDITIONAL", "mzk1Lemma22_induction_of_base / mzk1Lemma22_target_of_base") ]

theorem stepProviderRows_length : stepProviderRows.length = 4 := rfl

#check stepProvider_holds
#check mzk1Lemma22_induction_of_base
#check mzk1Lemma22_target_of_base

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepProviderProofActual
end
