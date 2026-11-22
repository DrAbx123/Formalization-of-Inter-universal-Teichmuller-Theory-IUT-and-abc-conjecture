import tmp.sheaf.xif.paper.Mzk1Lemma22HypPreservationActual
import tmp.sheaf.xif.paper.Mzk1GChoiceUnramifiedActual
import tmp.sheaf.xif.paper.Mzk1Lemma21RatioSquaredActual
import Mathlib.Tactic

/-! # Mzk1Lemma22HypPreservationSeparationActual — separation component of H-preservation

STEP 0 prior-art: reuse Mzk1Lemma22HypPreservationActual (GREEN 14 decls: fq_nonneg/f0q_eq_zero/
g_eval/fq_ge_two_of_ge_two/fq_le_one_of_mem_unit/fq_pos_* + target_* components),
Mzk1GChoiceUnramifiedActual (fq_zero/fq_one), Mzk1Lemma21RatioSquaredActual
(belyi21R_ratio_ge_sq), Mzk1GChoiceIntegrationActual (Mzk1ScaleData partition/hsep/lam/alpha2).
Proves the remaining separation component (Even n). No fake. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationSeparationActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioSquaredActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual

theorem fq_ge_two_of_ge_two (D : Mzk1ScaleData) {y : ℚ} (hy : 2 ≤ y) : 2 ≤ fq D.m D.n y := by
  have hy1 : 1 ≤ y := by linarith
  have h1 : 2 ≤ y ^ D.m := by
    calc (2 : ℚ) ≤ y := hy
      _ = y ^ 1 := by ring
      _ ≤ y ^ D.m := pow_le_pow_right₀ hy1 D.hm
  have h2 : 1 ≤ (y - 1) ^ D.n := one_le_pow₀ (by linarith)
  unfold fq
  have hpos : 0 < y ^ D.m := pow_pos (by linarith) D.m
  have hpos2 : 0 < (y - 1) ^ D.n := by linarith
  nlinarith

theorem fq_le_one_of_mem_unit (D : Mzk1ScaleData) (hne : Even D.n) {r : ℚ}
    (hr0 : 0 < r) (hr1 : r < 1) : fq D.m D.n r ≤ 1 := by
  have hne' : (r - 1) ^ D.n = (1 - r) ^ D.n := by
    have h : r - 1 = -(1 - r) := by ring
    rw [h, Even.neg_pow hne]
  unfold fq
  rw [hne']
  have hb0 : 0 ≤ 1 - r := by linarith
  have hb1 : 1 - r ≤ 1 := by linarith
  have h1 : r ^ D.m ≤ 1 := pow_le_one₀ (le_of_lt hr0) (le_of_lt hr1)
  have h2 : (1 - r) ^ D.n ≤ 1 := pow_le_one₀ hb0 hb1
  have h2n : 0 ≤ (1 - r) ^ D.n := pow_nonneg hb0 D.n
  nlinarith

theorem lam_b_ge_two (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta) :
    2 ≤ D.lam * D.b := by
  obtain ⟨h0S, hInfS, hpos, hβnotin, hsep⟩ := H
  obtain ⟨a, b, hpa, hpb, h2⟩ := hsep (P1Point.ofFinite D.alpha2) D.halpha2S
    (by
      intro h
      have : D.alpha2 = 0 := by simpa [P1Point.ofFinite] using h
      linarith [D.halpha2_pos])
    (P1Point.ofFinite_ne_infty D.alpha2)
  have hb : b = D.b := by
    have : P1Point.ofFinite b = P1Point.ofFinite D.b := by rw [← hpb, D.beta_eq]
    simpa [P1Point.ofFinite] using this
  have hpa' : D.alpha2 = a := by simpa [P1Point.ofFinite] using hpa
  have ha : a = D.alpha2 := hpa'.symm
  rw [ha, hb] at h2
  simpa [D.lam_eq, div_eq_inv_mul] using h2

theorem hyp_separation (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta)
    (hne : Even D.n) : HypPreservationSeparation D := by
  intro p hp hp0 hpin
  obtain ⟨h0S, hInfS, hpos, hβnotin, hsep⟩ := H
  obtain ⟨s, hs, hsp⟩ := Finset.mem_image.mp hp
  have hβfin : D.beta = P1Point.ofFinite D.b := D.beta_eq
  have hβ' : polyMapPoints (gPoly D) D.beta = P1Point.ofFinite ((gPoly D).eval D.b) := by
    simp [polyMapPoints, hβfin, P1Point.ofFinite]
  cases s with
  | none => exact absurd (by simpa [polyMapPoints, P1Point.infty] using hsp.symm) hpin
  | some u =>
      have hpu : p = P1Point.ofFinite ((gPoly D).eval u) := by
        simpa [polyMapPoints, P1Point.ofFinite] using hsp.symm
      have hva : (gPoly D).eval u = fq D.m D.n (D.lam * u) := g_eval D hne u
      have hvb : (gPoly D).eval D.b = fq D.m D.n (D.lam * D.b) := g_eval D hne D.b
      have ha_ne : fq D.m D.n (D.lam * u) ≠ 0 := by
        rw [← hva]
        intro h0; apply hp0; rw [hpu, h0]
      refine ⟨(gPoly D).eval u, (gPoly D).eval D.b, hpu, hβ', ?_⟩
      rw [hva, hvb]
      have hmem : P1Point.ofFinite u ∈ D.S := hs
      have hu0 : P1Point.ofFinite u ≠ P1Point.ofFinite (0 : ℚ) := by
        intro h
        apply ha_ne
        have : u = 0 := by simpa [P1Point.ofFinite] using h
        rw [this, mul_zero]; exact fq_zero D
      have hinf : P1Point.ofFinite u ≠ P1Point.infty := P1Point.ofFinite_ne_infty u
      rcases D.partition (P1Point.ofFinite u) hmem hu0 hinf with h1 | h2 | h3
      · have hua1 : u = D.alpha1 := by simpa [P1Point.ofFinite] using h1
        have hlamu : D.lam * u = D.r := by
          rw [hua1, D.lam_eq, D.r_eq, div_eq_inv_mul]
        rw [hlamu]
        have hr0Q : (0 : ℚ) < D.r := by exact_mod_cast D.hr0
        have hr1Q : D.r < (1 : ℚ) := by exact_mod_cast D.hr1
        have hle1 : fq D.m D.n D.r ≤ 1 := fq_le_one_of_mem_unit D hne hr0Q hr1Q
        have hge2 : 2 ≤ fq D.m D.n (D.lam * D.b) :=
          fq_ge_two_of_ge_two D (lam_b_ge_two D ⟨h0S, hInfS, hpos, hβnotin, hsep⟩)
        have hfrpos : 0 < fq D.m D.n D.r := fq_pos_of_mem_unit D hne hr0Q hr1Q
        rw [le_div_iff₀ hfrpos]
        nlinarith
      · have hua2 : u = D.alpha2 := by simpa [P1Point.ofFinite] using h2
        exfalso
        apply ha_ne
        rw [hua2, D.hlam_alpha2, fq_one D]
      · obtain ⟨x, hux, hxgt⟩ := h3
        have hux' : u = x := by simpa [P1Point.ofFinite] using hux
        have hxpos : 0 < x := lt_trans D.halpha2_pos hxgt
        have hxS : P1Point.ofFinite x ∈ D.S := by
          rw [← hux']
          exact hmem
        obtain ⟨a, b, hpa, hpb, hsep2⟩ := hsep (P1Point.ofFinite x) hxS
          (by
            intro h
            have hx0 : x = 0 := by simpa [P1Point.ofFinite] using h
            linarith [hxgt, hx0, D.halpha2_pos])
          (P1Point.ofFinite_ne_infty x)
        have hb : b = D.b := by
          have : P1Point.ofFinite b = P1Point.ofFinite D.b := by rw [← hpb, D.beta_eq]
          simpa [P1Point.ofFinite] using this
        have hpa' : x = a := by simpa [P1Point.ofFinite] using hpa
        have ha : a = x := hpa'.symm
        rw [ha, hb] at hsep2
        rw [hux']
        have hα2 : (0 : ℝ) < (D.alpha2 : ℝ) := by exact_mod_cast D.halpha2_pos
        have hcastx : ((D.lam * x : ℚ) : ℝ) = (x : ℝ) / (D.alpha2 : ℝ) := by
          rw [D.lam_eq]
          push_cast
          rw [div_eq_inv_mul]
        have hcastb : ((D.lam * D.b : ℚ) : ℝ) = (D.b : ℝ) / (D.alpha2 : ℝ) := by
          rw [D.lam_eq]
          push_cast
          rw [div_eq_inv_mul]
        have hx1 : (1 : ℝ) < ((D.lam * x : ℚ) : ℝ) := by
          rw [hcastx, lt_div_iff₀ hα2]
          have hxgtR : ((D.alpha2 : ℚ) : ℝ) < (x : ℝ) := by exact_mod_cast hxgt
          simpa using hxgtR
        have hblt : ((D.lam * x : ℚ) : ℝ) < ((D.lam * D.b : ℚ) : ℝ) := by
          rw [hcastx, hcastb, div_lt_div_iff_of_pos_right hα2]
          have h2xQ : 2 * x ≤ D.b := (le_div_iff₀ hxpos).mp hsep2
          have h2x : ((2 * x : ℚ) : ℝ) ≤ (D.b : ℝ) := by exact_mod_cast h2xQ
          push_cast at h2x
          have hxposR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxpos
          linarith
        have hratioR : (2 : ℝ) ≤ ((D.lam * D.b : ℚ) : ℝ) / ((D.lam * x : ℚ) : ℝ) := by
          rw [hcastb, hcastx, div_div_div_cancel_right₀ (ne_of_gt hα2)]
          exact_mod_cast hsep2
        have hsq := belyi21R_ratio_ge_sq D.hm D.hn hx1 hblt
        have h4 : (4 : ℝ) ≤ (((D.lam * D.b : ℚ) : ℝ) / ((D.lam * x : ℚ) : ℝ)) ^ 2 := by
          have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hratioR 2
          norm_num at h ⊢
          exact h
        have hfα_nonneg : 0 ≤ belyi21R D.m D.n ((D.lam * x : ℚ) : ℝ) := by
          unfold belyi21R
          exact mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
        have hstep1 : 2 * belyi21R D.m D.n ((D.lam * x : ℚ) : ℝ) ≤
            (((D.lam * D.b : ℚ) : ℝ) / ((D.lam * x : ℚ) : ℝ)) ^ 2 *
              belyi21R D.m D.n ((D.lam * x : ℚ) : ℝ) := by
          have hb := mul_le_mul_of_nonneg_right h4 hfα_nonneg
          nlinarith [hb, hfα_nonneg]
        have hreal : 2 * belyi21R D.m D.n ((D.lam * x : ℚ) : ℝ) ≤
            belyi21R D.m D.n ((D.lam * D.b : ℚ) : ℝ) :=
          le_trans hstep1 hsq
        have hQ : (2 : ℚ) * fq D.m D.n (D.lam * x) ≤ fq D.m D.n (D.lam * D.b) := by
          have h := hreal
          rw [← fq_coe D.m D.n (D.lam * x), ← fq_coe D.m D.n (D.lam * D.b)] at h
          exact_mod_cast h
        have hx1Q : (1 : ℚ) < D.lam * x := by exact_mod_cast hx1
        have hfqpos : 0 < fq D.m D.n (D.lam * x) := fq_pos_of_one_lt hx1Q
        rw [le_div_iff₀ hfqpos]
        exact hQ

#check lam_b_ge_two
#check hyp_separation

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationSeparationActual
end
