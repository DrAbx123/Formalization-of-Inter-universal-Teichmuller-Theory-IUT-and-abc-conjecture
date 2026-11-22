import tmp.sheaf.xif.paper.Mzk1GChoiceUnramifiedActual
import tmp.sheaf.xif.paper.Mzk1GChoiceUnramifiedCanonicalActual
import tmp.sheaf.xif.paper.Mzk1GChoiceAvoidCanonicalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-!
# Mzk1GChoiceCriticalInTargetActual — LAST unramified gate: critical points of gPoly map into target

STEP 0 prior-art (reuse, no re-proof): corpus [Mzk1] Lemma 2.1 (b) (critical points of
f(x)=x^m(x-1)^n are 0,1,r=m/(m+n)) and Lemma 2.2's target S' = f(S) union f(critical points);
stage4 Mzk1GChoiceUnramifiedActual (gPoly_derivative_eval, gPoly_derivative_zero_cases:
gPoly'(x)=0 => lam*x = 0 or 1 or r; lam_mul_alpha1; fq_zero/fq_one); stage4
Mzk1GChoiceConstruct/Integration (Mzk1ScaleData, gPoly_eval/gPoly_eval_zero/
gPoly_eval_alpha2/gPoly_collapse); stepxi Mzk1GChoiceUnramifiedCanonicalActual
(GChoiceCriticalInTarget/GChoiceDataUnramifiedShape/gChoice_unramified_of_criticalInTarget)
and Mzk1GChoiceAvoidCanonicalActual (gChoiceData_of_avoids: card+avoids PROVED).

THIS FILE closes GChoiceCriticalInTarget: every critical point of gPoly is one of
0, alpha2, alpha1 (all in S), and its image equals g(0), g(alpha2) or g(alpha1) — hence
lies in the image target.  Consequently GChoiceDataUnramifiedShape holds, and packaging
with the avoid file gives the full Mzk1GChoiceData (havoids+hcard+hunram all PROVED).
Registry frozen 14041; no registry edits.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceCriticalInTargetActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceDataActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedCanonicalActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceAvoidCanonicalActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual

/-- lam != 0 (stage4 helper). -/
theorem lam_ne_zero_critical (D : Mzk1ScaleData) : D.lam ≠ 0 := lam_ne_zero' D

/-- Image membership helper: if a point y in S, the map-point ofFinite (eval y) is in
the image target. -/
theorem eval_mem_image_of_mem {D : Mzk1ScaleData} {y : ℚ}
    (hy : P1Point.ofFinite y ∈ D.S) :
    P1Point.ofFinite ((gPoly D).eval y) ∈
      (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ)) :=
  Finset.mem_coe.mpr (Finset.mem_image_of_mem (polyMapPoints (gPoly D))
    (by simpa using hy))

/-- **Critical points map into the target (PROVED).** -/
theorem gChoiceCriticalInTarget_proved (D : Mzk1ScaleData)
    (H : Lemma22Hypotheses D.S D.beta) : GChoiceCriticalInTarget D := by
  intro p hp
  have h0S : P1Point.ofFinite (0 : ℚ) ∈ D.S := H.1
  cases p with
  | none =>
      have hg : gPoly D = 0 := by
        simpa [polyUnramifiedAt, P1Point.infty, not_ne_iff] using hp
      exact absurd hg (gPoly_ne_zero D)
  | some x =>
      have hderiv : (gPoly D).derivative.eval x = 0 := by
        have := hp
        simpa [polyUnramifiedAt] using not_not.mp this
      have hlam : D.lam ≠ 0 := lam_ne_zero_critical D
      rcases gPoly_derivative_zero_cases D hderiv with h0 | h1 | hr
      · have hx0 : x = 0 := by
          rcases mul_eq_zero.mp h0 with h | h
          · exact absurd h hlam
          · exact h
        show (polyMorphism (gPoly D) (gPoly_natDegree_pos D)).mapPoints
          (P1Point.ofFinite x) ∈
            (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ))
        rw [hx0]
        show P1Point.ofFinite ((gPoly D).eval 0) ∈ _
        exact eval_mem_image_of_mem h0S
      · have hxalpha : x = D.alpha2 := by
          have h : D.lam * x = D.lam * D.alpha2 := by
            rw [h1]
            exact D.hlam_alpha2.symm
          exact mul_left_cancel₀ hlam h
        show (polyMorphism (gPoly D) (gPoly_natDegree_pos D)).mapPoints
          (P1Point.ofFinite x) ∈
            (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ))
        rw [hxalpha]
        show P1Point.ofFinite ((gPoly D).eval D.alpha2) ∈ _
        exact eval_mem_image_of_mem D.halpha2S
      · have hmn : (((D.m + D.n : ℕ)) : ℚ) ≠ 0 := by
          have hm : 1 ≤ D.m := D.hm
          have hn : 1 ≤ D.n := D.hn
          have hpos : 0 < D.m + D.n := by omega
          exact_mod_cast (Nat.ne_of_gt hpos)
        have hr' : (D.lam * x) * (((D.m + D.n : ℕ)) : ℚ) = (D.m : ℚ) := by
          rw [mul_comm]
          exact hr
        have hsl : D.lam * x = (D.m : ℚ) / ((D.m + D.n : ℕ) : ℚ) := by
          rw [eq_div_iff hmn]
          exact hr'
        have hrq : D.r = (D.m : ℚ) / ((D.m + D.n : ℕ) : ℚ) := by
          rw [D.r_eq]
          have h := D.hr_eq
          rw [D.r_eq] at h
          have hQ : ((D.alpha1 / D.alpha2 : ℚ) : ℝ) =
              (((D.m : ℚ) / ((D.m + D.n : ℕ) : ℚ)) : ℝ) := by
            rw [h]
            push_cast
            ring
          exact_mod_cast hQ
        have hlamalpha : D.lam * D.alpha1 = D.r := lam_mul_alpha1 D
        have hxalpha1 : x = D.alpha1 := by
          have h : D.lam * x = D.lam * D.alpha1 := by
            rw [hsl, ← hrq]
            exact hlamalpha.symm
          exact mul_left_cancel₀ hlam h
        show (polyMorphism (gPoly D) (gPoly_natDegree_pos D)).mapPoints
          (P1Point.ofFinite x) ∈
            (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ))
        rw [hxalpha1]
        show P1Point.ofFinite ((gPoly D).eval D.alpha1) ∈ _
        exact eval_mem_image_of_mem D.halpha1S


/-- The unramified shape of the avoid file (same target), proved from the critical-point
theorem. -/
theorem gChoice_unramifiedShape_proved (D : Mzk1ScaleData)
    (H : Lemma22Hypotheses D.S D.beta) : GChoiceUnramifiedShape D :=
  Mzk1GChoiceUnramifiedCanonicalActual.gChoice_unramified_of_criticalInTarget D
    (gChoiceCriticalInTarget_proved D H)

/-- **FINAL g-choice DATA (all fields PROVED):** card collapse + avoids + unramified —
no named gates remain for Mzk1GChoiceData. -/
noncomputable def gChoiceData_complete (D : Mzk1ScaleData)
    (H : Lemma22Hypotheses D.S D.beta) : Mzk1GChoiceData :=
  Mzk1GChoiceAvoidCanonicalActual.gChoiceData_of_avoids D H
    (gChoice_unramifiedShape_proved D H)

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceCriticalInTargetActual

end
