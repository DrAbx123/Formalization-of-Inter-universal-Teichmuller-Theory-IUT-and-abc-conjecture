import tmp.sheaf.xif.paper.Mzk1GChoiceIntegrationActual
import tmp.sheaf.xif.paper.Mzk1Lemma21ImageActual
import tmp.sheaf.xif.paper.Mzk1GChoiceScaleActual
import tmp.sheaf.xif.paper.Mzk1BelyiCanonicalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-!
# Mzk1GChoiceAvoidCanonicalActual — avoids + data packaging for the g-choice step

STEP 0 prior-art (reuse, no re-proof): corpus [Mzk1] Lemma 2.1 (c)/(d) and Lemma 2.2
step (lines 106-135); stage4 Mzk1Lemma22GChoiceConstructActual (Mzk1ScaleData, fq,
f0q, gPoly, gPoly_eval/gPoly_eval_zero/gPoly_collapse; Mzk1Lemma22GChoiceDataActual
(Mzk1GChoiceData, gChoiceStep)); Mzk1GChoiceIntegrationActual (Mzk1ScaleData.ofScale,
beta_finite, sep_form); Mzk1Lemma21ImageActual.belyi21R_not_mem_image (PROVED real
separation: for the scaled real set with beta >= 2, belyi21R alpha != belyi21R beta);
Mzk1Lemma22GChoiceCard/StepConstruction (card collapse machinery);
Mzk1BelyiCanonicalActual (canonical TauCeti B_{m,n} critical values in {0,1}; supplies
the canonical Belyi control row for the unramified side).

THIS FILE (parallel to stage4's red Mzk1GChoiceAvoidActual; no edit to his files):
* gChoice_card_lt: gPoly collapses 0 and alpha2 (g(0)=g(alpha2)=f0q), so the image has
  strictly smaller cardinality (lemma22Step_card_lt/collision);
* gChoice_avoids: gPoly(b) is NOT in the image of gPoly on S — the scaled real
  separation row (belyi21R_not_mem_image) at scaled x = lam*x vs scaled beta = realBeta,
  with beta/alpha >= 2 from Lemma22Hypotheses (via D.hsep at 1);
* GChoiceUnramifiedShape (named shape) + canonical Belyi critical-values row;
* gChoiceData_of_avoids: package Mzk1GChoiceData with havoids PROVED and hunram as the
  named shape (stage4's remaining unramified proof fills it).
HONEST SCOPE: avoids + card + packaging proved; unramified remains a named shape (the
stage4 unramified proof is the remaining gate). No closure claim.
Registry frozen 14041; no registry edits.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceAvoidCanonicalActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21ImageActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceDataActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22StepConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22ProofActual
open TauCeti

/-- lam != 0 (lambda = alpha2^{-1}). -/
theorem gChoiceScaleData_lam_ne_zero (D : Mzk1ScaleData) : D.lam ≠ 0 := by
  rw [D.lam_eq]
  exact inv_ne_zero D.halpha2_ne

/-- beta >= 2 in real form (from the separation row at the scaled point 1). -/
theorem gChoiceScaleData_realBeta_ge_two (D : Mzk1ScaleData) : 2 ≤ D.realBeta := by
  have h := D.hsep (1 : ℝ) D.h1 (by norm_num)
  simpa using h

/-- belyi21R m n realBeta >= 2 for realBeta >= 2 (image-lemma estimate). -/
theorem gChoiceScaleData_belyi21R_realBeta_ge_two (D : Mzk1ScaleData) :
    2 ≤ belyi21R D.m D.n D.realBeta := by
  have hβ2 : (2 : ℝ) ≤ D.realBeta := gChoiceScaleData_realBeta_ge_two D
  unfold belyi21R
  have hβm : (2 : ℝ) ≤ D.realBeta ^ D.m := by
    calc (2 : ℝ) ≤ D.realBeta := hβ2
      _ = D.realBeta ^ 1 := by ring
      _ ≤ D.realBeta ^ D.m := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ D.realBeta) D.hm
  have hβn : 1 ≤ (D.realBeta - 1) ^ D.n :=
    one_le_pow₀ (by linarith : (1 : ℝ) ≤ D.realBeta - 1)
  have hβnpos : 0 < (D.realBeta - 1) ^ D.n := by linarith
  nlinarith [hβm, hβn, hβnpos]

/-- **Card collapse for gPoly:** g(0) = f0q = g(alpha2), 0 != alpha2 and both in S, so
the image of S under g has strictly smaller cardinality (the STEP |S'| < |S|). -/
theorem gChoice_card_lt (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta) :
    (D.S.image (polyMapPoints (gPoly D))).card < D.S.card := by
  obtain ⟨h0S, hInfS, hpos, hβnotin, hsep⟩ := H
  have hcol : polyMapPoints (gPoly D) (P1Point.ofFinite (0 : ℚ)) =
      polyMapPoints (gPoly D) (P1Point.ofFinite D.alpha2) := by
    show P1Point.ofFinite ((gPoly D).eval 0) = P1Point.ofFinite ((gPoly D).eval D.alpha2)
    rw [gPoly_collapse D D.hlam_alpha2]
  have h01 : P1Point.ofFinite (0 : ℚ) ≠ P1Point.ofFinite D.alpha2 := by
    intro h
    have h0 : (0 : ℚ) = D.alpha2 := by simpa [P1Point.ofFinite] using h
    exact D.halpha2_ne h0.symm
  exact card_image_lt_of_collision D.S (polyMapPoints (gPoly D)) h0S D.halpha2S h01 hcol

/-- The named unramified shape for gPoly (stage4 Mzk1GChoiceData.hunram). -/
def GChoiceUnramifiedShape (D : Mzk1ScaleData) : Prop :=
  UnramifiedOver (polyMorphism (gPoly D) (gPoly_natDegree_pos D))
    {p | p ∉ (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ))}
    (polyUnramifiedAt (gPoly D))

/-- Canonical Belyi critical-values control row (from Mzk1BelyiCanonicalActual). -/
theorem gChoice_canonicalBelyi_criticalValues (m n : ℕ) :
    (belyiPolynomial ℚ m n).criticalValues ℚ ⊆ ({0, 1} : Set ℚ) :=
  LeanFormal.IUT.XiFPaper.Mzk1BelyiCanonicalActual.belyi_criticalValues_subset m n

/-- **Avoids (PROVED):** g(b) is not in the image of g on S. -/
theorem gChoice_avoids (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta) :
    AvoidsPoint (polyMorphism (gPoly D) (gPoly_natDegree_pos D)) D.beta
      (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ)) := by
  obtain ⟨h0S, hInfS, hpos, hβnotin, hsep'⟩ := H
  intro hmem
  rw [Finset.mem_coe] at hmem
  obtain ⟨p, hpS, hpeq⟩ := Finset.mem_image.mp hmem
  have hmapβ : (polyMorphism (gPoly D) (gPoly_natDegree_pos D)).mapPoints D.beta =
      P1Point.ofFinite ((gPoly D).eval D.b) := by
    show polyMapPoints (gPoly D) D.beta = P1Point.ofFinite ((gPoly D).eval D.b)
    simp [polyMapPoints, P1Point.ofFinite, D.beta_eq]
  rw [hmapβ] at hpeq
  have hβ2 : (2 : ℝ) ≤ D.realBeta := gChoiceScaleData_realBeta_ge_two D
  have hb21 : 2 ≤ belyi21R D.m D.n D.realBeta :=
    gChoiceScaleData_belyi21R_realBeta_ge_two D
  cases p with
  | none =>
      have hne : P1Point.infty ≠ P1Point.ofFinite ((gPoly D).eval D.b) := by
        simp [P1Point.infty, P1Point.ofFinite]
      exact hne hpeq
  | some x =>
      have hxS : P1Point.ofFinite x ∈ D.S := hpS
      have hxeq : (gPoly D).eval x = (gPoly D).eval D.b := by
        have h := hpeq
        rw [show polyMapPoints (gPoly D) (some x) = P1Point.ofFinite ((gPoly D).eval x)
          from rfl] at h
        simpa [P1Point.ofFinite] using h
      have hcast_eval : ∀ y : ℚ, (((gPoly D).eval y : ℚ) : ℝ) =
          belyi21R D.m D.n ((D.lam : ℝ) * (y : ℝ)) +
            belyi22f0 (m := D.m) (n := D.n) D.scaledRealS D.hSne := by
        intro y
        rw [gPoly_eval]
        push_cast
        rw [fq_coe, f0q_coe]
        push_cast
        ring
      by_cases hx0 : x = 0
      · have hfqpos : 0 < fq D.m D.n (D.lam * D.b) := by
          have hcast : ((fq D.m D.n (D.lam * D.b) : ℚ) : ℝ) =
              belyi21R D.m D.n D.realBeta := by
            rw [fq_coe, D.realBeta_eq]
          have hposR : (0 : ℝ) < ((fq D.m D.n (D.lam * D.b) : ℚ) : ℝ) := by
            rw [hcast]
            linarith
          exact_mod_cast hposR
        rw [hx0] at hxeq
        rw [gPoly_eval_zero D, gPoly_eval] at hxeq
        have hfq0 : fq D.m D.n (D.lam * D.b) = 0 := by linarith
        exact hfqpos.ne' hfq0
      · have hxpos : 0 < x := by
          obtain ⟨y, hpy, hypos⟩ := hpos (P1Point.ofFinite x) hxS
            (by intro h; exact hx0 (by simpa [P1Point.ofFinite] using h))
            (by simp [P1Point.infty, P1Point.ofFinite])
          have hxy : x = y := by simpa [P1Point.ofFinite] using hpy
          rwa [hxy]
        have hscaled : ((D.lam * x : ℚ) : ℝ) ∈ D.scaledRealS :=
          D.mem_scaledRealS_of_mem (P1Point.ofFinite x) hxS
            (by simp [P1Point.infty, P1Point.ofFinite]) x rfl hxpos
        have hscaled_ne0 : ((D.lam * x : ℚ) : ℝ) ≠ 0 := by
          have hne : D.lam * x ≠ 0 :=
            mul_ne_zero (gChoiceScaleData_lam_ne_zero D) (ne_of_gt hxpos)
          exact_mod_cast hne
        have hneq : belyi21R D.m D.n ((D.lam * x : ℚ) : ℝ) ≠
            belyi21R D.m D.n D.realBeta :=
          belyi21R_not_mem_image D.hm D.hn D.scaledRealS D.realBeta ((D.r : ℚ) : ℝ)
            D.h0 D.h1 D.hr D.hr0 D.hr1 D.hbig hβ2 D.hsep
            ((D.lam * x : ℚ) : ℝ) hscaled
        have hcast := congrArg (fun q : ℚ => (q : ℝ)) hxeq
        rw [hcast_eval x, hcast_eval D.b] at hcast
        have hbarg : (D.lam : ℝ) * (D.b : ℝ) = D.realBeta := by
          rw [D.realBeta_eq]
          push_cast
          ring
        rw [hbarg] at hcast
        have hxarg : ((D.lam * x : ℚ) : ℝ) = (D.lam : ℝ) * (x : ℝ) := by
          push_cast
          ring
        rw [hxarg] at hneq
        exact hneq (by linarith)

/-- Package a Mzk1GChoiceData from the proved avoids + card and the named unramified
shape (stage4 fills hunram; everything else is proved here). -/
noncomputable def gChoiceData_of_avoids (D : Mzk1ScaleData)
    (H : Lemma22Hypotheses D.S D.beta) (hunram : GChoiceUnramifiedShape D) :
    Mzk1GChoiceData where
  S := D.S
  beta := D.beta
  g := gPoly D
  hdeg := gPoly_natDegree_pos D
  hcard := gChoice_card_lt D H
  havoids := gChoice_avoids D H
  hunram := hunram

/-- Rows: (g-choice component, Lean evidence, status). -/
def mzk1GChoiceAvoidRows : List (String × String × String) :=
  [ ("card collapse g(0)=g(alpha2)", "gChoice_card_lt (collision; gPoly_collapse)", "PROVED"),
    ("avoids g(b) not in image", "gChoice_avoids (belyi21R_not_mem_image on scaled real set; beta/alpha>=2 from H)", "PROVED"),
    ("canonical Belyi critical-value control", "gChoice_canonicalBelyi_criticalValues (Mzk1BelyiCanonicalActual)", "PROVED (reuse)"),
    ("unramified over complement of image", "GChoiceUnramifiedShape (named shape; stage4 unramified proof fills)", "NAMED SHAPE"),
    ("Mzk1GChoiceData packaging", "gChoiceData_of_avoids (havoids+hcard PROVED, hunram named)", "PROVED (conditional on hunram)"),
    ("g-choice lambda/scaling", "Mzk1GChoiceScaleActual v5 (scaleOrdering/scale_realHypotheses_exists; integration ofScale)", "PROVED"),
    ("conditioned forall / Thm 2.5", "stage4 chain (h22 proof; stage4 owns)", "OPEN (as before)") ]

theorem mzk1GChoiceAvoidRows_length : mzk1GChoiceAvoidRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceAvoidCanonicalActual

end
