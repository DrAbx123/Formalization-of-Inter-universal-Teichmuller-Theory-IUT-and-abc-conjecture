import tmp.sheaf.xif.paper.Mzk1Lemma22GChoiceConstructActual
import tmp.sheaf.xif.paper.Mzk1GChoiceScaleActual
import tmp.sheaf.xif.paper.Mzk1GChoiceCardActual
import Mathlib.Tactic

/-! # Mzk1GChoiceIntegrationActual — build Mzk1ScaleData from stepxi scale v3 + ScaleOrdering

STEP 0 prior-art: resume priority (Lead).  Reuse (no re-proof):
stepxi Mzk1GChoiceScaleActual v3 GREEN/CITABLE (scaleP/scaleS/ScaleOrdering/scaleRatS/scaleRealS/
scale_realHypotheses_exists — ScaleRealHypotheses PROVED), stage4 Mzk1Lemma22GChoiceConstructActual
(Mzk1ScaleData consumer package), Mzk1GChoiceCardActual (card collapse), Mzk1GChoiceDegreeActual.
This file assembles the consumer data from the proved scale package. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceIntegrationActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual

/-- Build the consumer Mzk1ScaleData from stepxi's proved scale_realHypotheses_exists. -/
noncomputable def Mzk1ScaleData.ofScale
    (S : Finset (P1Point ℚ)) (β : P1Point ℚ) (b : ℚ)
    (βeq : β = P1Point.ofFinite b)
    (O : ScaleOrdering S)
    (hpos : ∀ p ∈ S, p ≠ P1Point.ofFinite (0 : ℚ) → p ≠ P1Point.infty →
      ∃ x : ℚ, p = P1Point.ofFinite x ∧ 0 < x)
    (hsep : ∀ a : ℚ, P1Point.ofFinite a ∈ S → 0 < a → 2 ≤ b / a)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hEven : Even n)
    (hr : ((O.alpha1 / O.alpha2 : ℚ) : ℝ) = (m : ℝ) / ((m + n : ℕ) : ℝ)) :
    Mzk1ScaleData :=
  let H := scale_realHypotheses_exists S b O hpos hsep m n hm hn hr
  have H' : ScaleRealHypotheses S b O (scaleRealS O.alpha2⁻¹ S) := H
  { S := S
    beta := β
    b := b
    beta_eq := βeq
    alpha1 := O.alpha1
    alpha2 := O.alpha2
    lam := O.alpha2⁻¹
    lam_eq := rfl
    r := O.alpha1 / O.alpha2
    r_eq := rfl
    scaledRealS := scaleRealS O.alpha2⁻¹ S
    scaledRatS := scaleRatS O.alpha2⁻¹ S
    scaledRealS_eq := scaleRealS_eq_image O.alpha2⁻¹ S
    m := m
    n := n
    hm := hm
    hn := hn
    hSne := H'.2.1
    h0 := H'.2.2.1
    h1 := H'.2.2.2.1
    hr := H'.2.2.2.2.1
    hr0 := H'.2.2.2.2.2.1
    hr1 := H'.2.2.2.2.2.2.1
    hr_eq := hr
    hbig := H'.2.2.2.2.2.2.2.2.1
    realBeta := ((O.alpha2⁻¹ * b : ℚ) : ℝ)
    realBeta_eq := rfl
    hsep := H'.2.2.2.2.2.2.2.2.2
    hRatSne := by
      obtain ⟨x, hx⟩ := H'.2.1
      rw [scaleRealS_eq_image] at hx
      obtain ⟨q, hq, _⟩ := Finset.mem_image.mp hx
      exact ⟨q, hq⟩
    halpha1S := O.mem1
    halpha2S := O.mem2
    halpha2_ne := ne_of_gt (lt_trans O.pos1 O.lt)
    hlam_alpha2 := inv_mul_alpha2 (lt_trans O.pos1 O.lt)
    mem_scaledRealS_of_mem := by
      intro p hp hpin x hpx hxpos
      have hxS : P1Point.ofFinite x ∈ S := by rwa [hpx] at hp
      have h1 : P1Point.ofFinite (O.alpha2⁻¹ * x) ∈ scaleS O.alpha2⁻¹ S :=
        mem_scaleS_of_mem hxS
      have h2 : O.alpha2⁻¹ * x ∈ scaleRatS O.alpha2⁻¹ S :=
        mem_scaleRatS_of_mem_scaleS h1
      have h3 : ((O.alpha2⁻¹ * x : ℚ) : ℝ) ∈ scaleRealS O.alpha2⁻¹ S :=
        mem_scaleRealS_of_mem_scaleRatS h2
      simpa [scaleRealS_eq_image] using h3
    hn_even := hEven
    lam_pos := inv_pos.mpr (lt_trans O.pos1 O.lt)
    zero_mem_scaledRatS := by
      have h : P1Point.ofFinite (0 : ℚ) ∈ scaleS O.alpha2⁻¹ S := zero_mem_scaleS O.mem0
      simpa [scaleRatS] using mem_scaleRatS_of_mem_scaleS h
    scaledRatS_nonneg := by
      intro q hq
      unfold scaleRatS at hq
      obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
      rw [Finset.mem_erase] at hp
      have hpp : p ≠ P1Point.infty := hp.1
      cases p with
      | none =>
          have hq0 : q = 0 := by simpa using hpq.symm
          exact le_of_eq hq0.symm
      | some x =>
          obtain ⟨s, hs, hsp⟩ := Finset.mem_image.mp hp.2
          cases s with
          | none =>
              simp [scaleP] at hsp
          | some y =>
              have hxy : x = O.alpha2⁻¹ * y := by
                simpa [scaleP] using hsp.symm
              have hqeq : q = O.alpha2⁻¹ * y := by
                rw [hxy] at hpq
                exact hpq.symm
              have hyS : P1Point.ofFinite y ∈ S := hs
              have hynonneg : 0 ≤ y := by
                by_cases hy0 : y = 0
                · subst hy0; norm_num
                · obtain ⟨z, hz, hzpos⟩ := hpos (P1Point.ofFinite y) hyS
                    (by intro h; exact hy0 (by simpa [P1Point.ofFinite] using h))
                    (P1Point.ofFinite_ne_infty y)
                  have hyz : y = z := by simpa [P1Point.ofFinite] using hz
                  linarith
              rw [hqeq]
              exact mul_nonneg (le_of_lt (inv_pos.mpr (lt_trans O.pos1 O.lt))) hynonneg
    halpha1_pos := O.pos1
    halpha2_pos := lt_trans O.pos1 O.lt
    partition := O.partition }

/-- The constructed scale data has the paper n-even/odd shifted polynomial support:
record the value predicates for the next avoids/unramified batch. -/
theorem ofScale_lam_mul_alpha2 (S β b βeq O hpos hsep m n hm hn hEven hr) :
    (Mzk1ScaleData.ofScale S β b βeq O hpos hsep m n hm hn hEven hr).lam *
      (Mzk1ScaleData.ofScale S β b βeq O hpos hsep m n hm hn hEven hr).alpha2 = 1 := by
  show O.alpha2⁻¹ * O.alpha2 = 1
  exact inv_mul_alpha2 (lt_trans O.pos1 O.lt)


/-- Rational representation: any r in (0,1) is m/(m+n) with m,n >= 1. -/
theorem rat_rep (r : ℚ) (h0 : 0 < r) (h1 : r < 1) :
    ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧
      ((r : ℚ) : ℝ) = (m : ℝ) / ((m + n : ℕ) : ℝ) := by
  have hnumpos : 0 < r.num := Rat.num_pos.mpr h0
  have hnumlt : r.num < (r.den : ℤ) := Rat.num_lt_denom_iff.mpr h1
  set m : ℕ := r.num.natAbs with hm_def
  have hmZ : (m : ℤ) = r.num := Int.natAbs_of_nonneg (le_of_lt hnumpos)
  have hmpos : 0 < m := by omega
  have hmlt : m < r.den := by
    have : (m : ℤ) < (r.den : ℤ) := by rw [hmZ]; exact hnumlt
    exact_mod_cast this
  set n : ℕ := r.den - m with hn_def
  have hnpos : 0 < n := by omega
  have hden : m + n = r.den := by omega
  have hrepr : ((r : ℚ) : ℝ) = (m : ℝ) / ((m + n : ℕ) : ℝ) := by
    have hQ : (r : ℚ) = (m : ℚ) / ((m + n : ℕ) : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den r]
      rw [← hden]
      have hmQ : (m : ℚ) = (r.num : ℚ) := by exact_mod_cast hmZ
      rw [hmQ]
    rw [hQ]
    push_cast
    ring
  exact ⟨m, n, hmpos, hnpos, hrepr⟩


/-- Even-denominator rational representation: r = m/(m+n) with n even. -/
theorem rat_rep_even (r : ℚ) (h0 : 0 < r) (h1 : r < 1) :
    ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ Even n ∧
      ((r : ℚ) : ℝ) = (m : ℝ) / ((m + n : ℕ) : ℝ) := by
  obtain ⟨m, n, hm, hn, hr⟩ := rat_rep r h0 h1
  refine ⟨2 * m, 2 * n, by omega, by omega, ?_, ?_⟩
  · exact ⟨n, by ring⟩
  · have h2 : (2 * m : ℕ) + 2 * n = 2 * (m + n) := by ring
    rw [h2, hr]
    push_cast
    field_simp

/-- β finite extraction from Lemma22Hypotheses. -/
theorem beta_finite {S : Finset (P1Point ℚ)} {β : P1Point ℚ}
    (H : Lemma22Hypotheses S β) : ∃ b : ℚ, β = P1Point.ofFinite b := by
  obtain ⟨h0S, hInfS, hpos, hβnotin, hsep⟩ := H
  cases β with
  | none => exact absurd hInfS hβnotin
  | some b => exact ⟨b, rfl⟩

/-- Separation in the scale form (∀a with ofFinite a in S and 0<a: 2 ≤ b/a). -/
theorem sep_form {S : Finset (P1Point ℚ)} {β : P1Point ℚ} {b : ℚ}
    (H : Lemma22Hypotheses S β) (hβ : β = P1Point.ofFinite b) :
    ∀ a : ℚ, P1Point.ofFinite a ∈ S → 0 < a → 2 ≤ b / a := by
  obtain ⟨h0S, hInfS, hpos, hβnotin, hsep⟩ := H
  intro a ha hapos
  obtain ⟨a', b', hpa, hpb, h2⟩ := hsep (P1Point.ofFinite a) ha
    (fun h => by
      have : a = (0 : ℚ) := by simpa [P1Point.ofFinite] using h
      linarith)
    (P1Point.ofFinite_ne_infty a)
  have hpa' : a = a' := by simpa [P1Point.ofFinite] using hpa
  have ha' : a' = a := hpa'.symm
  have hb' : b' = b := by
    have : P1Point.ofFinite b' = P1Point.ofFinite b := by rw [← hpb, hβ]
    simpa [P1Point.ofFinite] using this
  rwa [ha', hb'] at h2

/-- Build the consumer scale data from Lemma22Hypotheses + cardinality bound, using
stepxi's Finset-min ScaleOrdering extraction and proved scale_realHypotheses_exists. -/
noncomputable def Mzk1ScaleData.ofHypotheses
    (S : Finset (P1Point ℚ)) (β : P1Point ℚ) (H : Lemma22Hypotheses S β)
    (hcard : 3 < S.card) : Mzk1ScaleData :=
  let b := Classical.choose (beta_finite H)
  let hb : β = P1Point.ofFinite b := Classical.choose_spec (beta_finite H)
  let O : ScaleOrdering S := scaleOrdering_of_hypotheses S β H hcard
  have hα2pos : 0 < O.alpha2 := lt_trans O.pos1 O.lt
  have hrpos : 0 < O.alpha1 / O.alpha2 := div_pos O.pos1 hα2pos
  have hrlt : O.alpha1 / O.alpha2 < 1 := by
    rw [div_lt_one hα2pos]
    exact O.lt
  let rep := rat_rep_even (O.alpha1 / O.alpha2) hrpos hrlt
  let m := Classical.choose rep
  have hspec : ∃ n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ Even n ∧
      ((O.alpha1 / O.alpha2 : ℚ) : ℝ) = (m : ℝ) / ((m + n : ℕ) : ℝ) :=
    Classical.choose_spec rep
  let n := Classical.choose hspec
  have hm : 1 ≤ m := (Classical.choose_spec hspec).1
  have hn : 1 ≤ n := (Classical.choose_spec hspec).2.1
  have hEven : Even n := (Classical.choose_spec hspec).2.2.1
  have hr : ((O.alpha1 / O.alpha2 : ℚ) : ℝ) = (m : ℝ) / ((m + n : ℕ) : ℝ) :=
    (Classical.choose_spec hspec).2.2.2
  Mzk1ScaleData.ofScale S β b hb O
    (fun p hp hp0 hpin => (H.2.2.1) p hp hp0 hpin)
    (sep_form H hb) m n hm hn hEven hr

#check rat_rep
#check beta_finite
#check sep_form
#check Mzk1ScaleData.ofHypotheses

#check Mzk1ScaleData.ofScale
#check ofScale_lam_mul_alpha2

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceIntegrationActual
end
