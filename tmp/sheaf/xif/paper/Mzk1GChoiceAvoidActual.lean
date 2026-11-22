import tmp.sheaf.xif.paper.Mzk1GChoiceIntegrationActual
import tmp.sheaf.xif.paper.Mzk1GChoiceCardActual
import tmp.sheaf.xif.paper.Mzk1GChoiceDegreeActual
import tmp.sheaf.xif.paper.Mzk1Lemma21ImageActual
import Mathlib.Tactic

/-! # Mzk1GChoiceAvoidActual — avoids for the g-choice step (scaled Lemma 2.1(c))

STEP 0 prior-art: resume priority (Lead).  Reuse: Mzk1Lemma22GChoiceConstructActual
(gPoly_eval, f0q_coe, Mzk1ScaleData), Mzk1GChoiceIntegrationActual (ofHypotheses),
Mzk1GChoiceDegreeActual (hdeg), Mzk1Lemma21ImageActual (belyi21R_not_mem_image PROVED),
corpus Lemma 2.1(c)/Lemma 2.2 step.  No fake. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceAvoidActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21ImageActual

/-- Avoids: g(beta) is not in the image of g on S (finite part; the step's target set). -/
theorem gChoice_avoids (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta) :
    AvoidsPoint (polyMorphism (gPoly D) (gPoly_natDegree_pos D)) D.beta
      (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ)) := by
  obtain ⟨h0S, hInfS, hpos, hβnotin, hsep'⟩ := H
  intro hmem
  obtain ⟨p, hpS, hpeq⟩ := Finset.mem_image.mp hmem
  -- beta is finite with value b
  have hβfin : D.beta = P1Point.ofFinite D.b := D.beta_eq
  cases p with
  | none =>
      -- p = infinity maps to infinity; beta maps to a finite value: contradiction
      have hnone : polyMapPoints (gPoly D) (none : P1Point ℚ) = none := rfl
      have hsome : (polyMorphism (gPoly D) (gPoly_natDegree_pos D)).mapPoints D.beta =
          some ((gPoly D).eval D.b) := by
        show polyMapPoints (gPoly D) D.beta = some ((gPoly D).eval D.b)
        simp [polyMapPoints, P1Point.ofFinite, D.beta_eq]
      rw [hnone, hsome] at hpeq
      exact Option.some_ne_none _ hpeq.symm
  | some x =>
      have hxS : P1Point.ofFinite x ∈ D.S := hpS
      have hmapβ : (polyMorphism (gPoly D) (gPoly_natDegree_pos D)).mapPoints D.beta =
          some ((gPoly D).eval D.b) := by
        show polyMapPoints (gPoly D) D.beta = some ((gPoly D).eval D.b)
        simp [polyMapPoints, P1Point.ofFinite, D.beta_eq]
      have hxy : (gPoly D).eval x = (gPoly D).eval D.b := by
        have h := hpeq
        rw [show polyMapPoints (gPoly D) (some x) = some ((gPoly D).eval x) from rfl,
          hmapβ] at h
        exact Option.some.inj h
      -- lambda * x lies in the scaled real set
      have hscaled : ((D.lam * x : ℚ) : ℝ) ∈ D.scaledRealS := by
        by_cases hx0 : x = 0
        · rw [hx0]
          have hzero : ((D.lam * (0 : ℚ) : ℚ) : ℝ) = (0 : ℝ) := by norm_num
          rw [hzero]
          exact D.h0
        · have hxpos : 0 < x := by
            obtain ⟨y, hy, hypos⟩ := hpos (P1Point.ofFinite x) hxS
              (by intro h; exact hx0 (by simpa [P1Point.ofFinite] using h))
              (P1Point.ofFinite_ne_infty x)
            have hxy' : x = y := by simpa [P1Point.ofFinite] using hy
            linarith
          exact D.mem_scaledRealS_of_mem (P1Point.ofFinite x) hxS
            (P1Point.ofFinite_ne_infty x) x rfl hxpos
      have hβ2 : 2 ≤ D.realBeta := by
        have h := D.hsep 1 D.h1 (by norm_num)
        simpa using h
      -- Lemma 2.1(c) on the scaled real set
      have himage := belyi21R_not_mem_image (m := D.m) (n := D.n) D.hm D.hn
        D.scaledRealS D.realBeta ((D.r : ℚ) : ℝ)
        D.h0 D.h1 D.hr D.hr0 D.hr1 D.hbig hβ2
        (fun α hα hα0 => D.hsep α hα hα0)
        ((D.lam * x : ℚ) : ℝ) hscaled
      -- equality of the real f-values
      have hqeq : fq D.m D.n (D.lam * x) = fq D.m D.n (D.lam * D.b) := by
        rw [gPoly_eval, gPoly_eval] at hxy
        linarith
      have hreal : belyi21R D.m D.n ((D.lam * x : ℚ) : ℝ) =
          belyi21R D.m D.n D.realBeta := by
        rw [D.realBeta_eq, ← fq_coe D.m D.n (D.lam * x),
          ← fq_coe D.m D.n (D.lam * D.b), hqeq]
      exact himage hreal

#check gChoice_avoids

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceAvoidActual
end
