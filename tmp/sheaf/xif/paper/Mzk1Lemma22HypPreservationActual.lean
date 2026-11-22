import tmp.sheaf.xif.paper.Mzk1GChoiceAvoidActual
import tmp.sheaf.xif.paper.Mzk1GChoiceDegreeActual
import tmp.sheaf.xif.paper.Mzk1GChoiceIntegrationActual
import tmp.sheaf.xif.paper.Mzk1Lemma21RatioSquaredActual
import tmp.sheaf.xif.paper.Mzk1GChoiceUnramifiedActual
import Mathlib.Tactic

/-! # Mzk1Lemma22HypPreservationActual — H-preservation for the g-choice step (Even n)

STEP 0 prior-art: terminal step plan approved. Reuse: Mzk1GChoiceAvoidActual (gChoice_avoids),
Mzk1GChoiceIntegrationActual (Mzk1ScaleData settings; Even n guaranteed by rat_rep_even),
Mzk1Lemma21RatioSquaredActual, Mzk1Lemma21RealActual.  This batch proves components
(1) 0 in target image, (2) infinity in target image, (3) positivity, (4) beta' not in image
(avoids); the separation component (5) is the remaining obligation (recorded). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceAvoidActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual

theorem fq_nonneg {m n : ℕ} (hne : Even n) {x : ℚ} (hx : 0 ≤ x) :
    0 ≤ fq m n x := by
  unfold fq
  exact mul_nonneg (pow_nonneg hx m) (Even.pow_nonneg hne (x - 1))

theorem fq_pos_of_one_lt {m n : ℕ} {x : ℚ} (hx : 1 < x) : 0 < fq m n x := by
  unfold fq
  exact mul_pos (pow_pos (by linarith) m) (pow_pos (by linarith) n)

theorem fq_pos_of_mem_unit (D : Mzk1ScaleData) (hne : Even D.n) {r : ℚ}
    (hr0 : 0 < r) (hr1 : r < 1) : 0 < fq D.m D.n r := by
  have hne' : (r - 1) ^ D.n = (1 - r) ^ D.n := by
    have h : r - 1 = -(1 - r) := by ring
    rw [h, Even.neg_pow hne]
  unfold fq
  rw [hne']
  exact mul_pos (pow_pos hr0 D.m) (pow_pos (by linarith) D.n)

theorem f0q_eq_zero (D : Mzk1ScaleData) (hne : Even D.n) : f0q D = 0 := by
  have hnonneg : ∀ q ∈ D.scaledRatS, 0 ≤ fq D.m D.n q :=
    fun q hq => fq_nonneg hne (D.scaledRatS_nonneg q hq)
  have hle : D.scaledRatS.inf' D.hRatSne (fun q => fq D.m D.n q) ≤ 0 := by
    have h := Finset.inf'_le (s := D.scaledRatS) (f := fun q => fq D.m D.n q)
      D.zero_mem_scaledRatS
    rwa [fq_zero D] at h
  have hge : 0 ≤ D.scaledRatS.inf' D.hRatSne (fun q => fq D.m D.n q) :=
    Finset.le_inf' D.hRatSne (fun q => fq D.m D.n q) hnonneg
  have h0 : D.scaledRatS.inf' D.hRatSne (fun q => fq D.m D.n q) = 0 :=
    le_antisymm hle hge
  unfold f0q
  rw [h0]
  ring

theorem g_eval (D : Mzk1ScaleData) (hne : Even D.n) (x : ℚ) :
    (gPoly D).eval x = fq D.m D.n (D.lam * x) := by
  rw [gPoly_eval, f0q_eq_zero D hne]
  ring

theorem g_zero (D : Mzk1ScaleData) (hne : Even D.n) : (gPoly D).eval 0 = 0 := by
  rw [g_eval D hne 0, show D.lam * 0 = 0 by ring, fq_zero D]

theorem target_zero_mem (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta)
    (hne : Even D.n) :
    P1Point.ofFinite (0 : ℚ) ∈ D.S.image (polyMapPoints (gPoly D)) := by
  obtain ⟨h0S, _hInfS, _hpos, _hβnotin, _hsep⟩ := H
  apply Finset.mem_image.mpr
  refine ⟨P1Point.ofFinite (0 : ℚ), h0S, ?_⟩
  show some ((gPoly D).eval 0) = some (0 : ℚ)
  rw [g_zero D hne]

theorem target_infty_mem (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta) :
    P1Point.infty ∈ D.S.image (polyMapPoints (gPoly D)) := by
  obtain ⟨_h0S, hInfS, _hpos, _hβnotin, _hsep⟩ := H
  apply Finset.mem_image.mpr
  refine ⟨P1Point.infty, hInfS, ?_⟩
  rfl

theorem target_positivity (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta)
    (hne : Even D.n) :
    ∀ p ∈ D.S.image (polyMapPoints (gPoly D)), p ≠ P1Point.ofFinite (0 : ℚ) →
      p ≠ P1Point.infty → ∃ x : ℚ, p = P1Point.ofFinite x ∧ 0 < x := by
  obtain ⟨_h0S, _hInfS, hpos, _hβnotin, _hsep⟩ := H
  intro p hp hp0 hpin
  obtain ⟨s, hs, hsp⟩ := Finset.mem_image.mp hp
  cases s with
  | none => exact absurd (by simpa [polyMapPoints, P1Point.infty] using hsp.symm) hpin
  | some u =>
      have hpu : p = P1Point.ofFinite ((gPoly D).eval u) := by
        simpa [polyMapPoints, P1Point.ofFinite] using hsp.symm
      have hval : (gPoly D).eval u = fq D.m D.n (D.lam * u) := g_eval D hne u
      have hune0 : (gPoly D).eval u ≠ 0 := by
        intro h0; apply hp0; rw [hpu, h0]
      have hfqne : fq D.m D.n (D.lam * u) ≠ 0 := by rw [← hval]; exact hune0
      have hupos : 0 ≤ u := by
        by_cases hu0 : u = 0
        · exfalso; apply hfqne; rw [hu0, mul_zero]; exact fq_zero D
        · obtain ⟨z, hz, hzpos⟩ := hpos (P1Point.ofFinite u) hs
            (by intro h; exact hu0 (by simpa [P1Point.ofFinite] using h))
            (P1Point.ofFinite_ne_infty u)
          have huz : u = z := by simpa [P1Point.ofFinite] using hz
          linarith
      have hlam_nonneg : 0 ≤ D.lam * u := mul_nonneg (le_of_lt D.lam_pos) hupos
      have hnonneg : 0 ≤ fq D.m D.n (D.lam * u) := fq_nonneg hne hlam_nonneg
      refine ⟨(gPoly D).eval u, hpu, ?_⟩
      rw [hval]
      exact lt_of_le_of_ne hnonneg (Ne.symm hfqne)

theorem target_beta_notin (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta) :
    polyMapPoints (gPoly D) D.beta ∉
      (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ)) :=
  gChoice_avoids D H


/-- Remaining separation component (recorded obligation, no fake): for every finite target
value b' with b' != 0, 2 <= beta'/b'. -/
def HypPreservationSeparation (D : Mzk1ScaleData) : Prop :=
  ∀ p ∈ D.S.image (polyMapPoints (gPoly D)), p ≠ P1Point.ofFinite (0 : ℚ) →
    p ≠ P1Point.infty → ∃ a b : ℚ, p = P1Point.ofFinite a ∧
      polyMapPoints (gPoly D) D.beta = P1Point.ofFinite b ∧ 2 ≤ b / a

structure HypPreservationRow where
  item : String
  status : String
  proved : Bool

def hypPreservationRows : List HypPreservationRow :=
  [ ⟨"fq_nonneg (Even n), f0q = 0, g_eval", "PROVED", true⟩,
    ⟨"0 in target image", "PROVED (target_zero_mem)", true⟩,
    ⟨"infinity in target image", "PROVED (target_infty_mem)", true⟩,
    ⟨"positivity of target points", "PROVED (target_positivity)", true⟩,
    ⟨"beta' not in target image (avoids)", "PROVED (target_beta_notin = gChoice_avoids)", true⟩,
    ⟨"beta'-separation (Even n, via partition + belyi21R_ratio_ge_sq)", "PENDING (HypPreservationSeparation)", false⟩ ]

theorem hypPreservationRows_length : hypPreservationRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationActual
end
