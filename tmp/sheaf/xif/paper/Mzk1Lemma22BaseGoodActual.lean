import tmp.sheaf.xif.paper.RestatedLemma22InterfaceActual
import tmp.sheaf.xif.paper.Mzk1GChoiceScaleActual
import tmp.sheaf.xif.paper.Mzk1GChoiceIntegrationActual
import Mathlib.Tactic

/-! # Mzk1Lemma22BaseGoodActual — base case of the flat Good induction (|S| <= 3)

STEP 0 prior-art: reuse stepxi RestatedLemma22InterfaceActual (Good/polyEvalP1/specialSet),
Mzk1GChoiceScaleActual (posRatS/mem_posRatS_of_mem/exists_of_mem_posRatS/posRatS_card),
Mzk1GChoiceIntegrationActual (beta_finite), Mzk1PolyMapActual.  Base polynomial is the
unified linear map f = C c * X (derivative = C c != 0, so the C-point unramified
condition holds automatically).  SCOPE (Lead A313): this is the F=Q component (rational inputs) of the paper's base case
m(S)=0; full Qbar scope = separate named reduction layers. No fake. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22BaseGoodActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceIntegrationActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual

/-- All points of S are 0 or infinity when posRatS is empty. -/
theorem eq_zero_or_infty_of_pos_card_zero {S : Finset (P1Point ℚ)}
    (h0S : P1Point.ofFinite (0 : ℚ) ∈ S) (hinfS : P1Point.infty ∈ S)
    (hpos : ∀ p ∈ S, p ≠ P1Point.ofFinite (0 : ℚ) → p ≠ P1Point.infty →
      ∃ x : ℚ, p = P1Point.ofFinite x ∧ 0 < x)
    (hz : (posRatS S).card = 0) :
    ∀ p ∈ S, p = P1Point.ofFinite (0 : ℚ) ∨ p = P1Point.infty := by
  intro p hp
  by_cases h0 : p = P1Point.ofFinite (0 : ℚ)
  · exact Or.inl h0
  by_cases hinf : p = P1Point.infty
  · exact Or.inr hinf
  · exfalso
    obtain ⟨x, hpx, hxpos⟩ := hpos p hp h0 hinf
    have hxmem : x ∈ posRatS S := mem_posRatS_of_mem hp h0 hinf hpx
    have hposcard : 0 < (posRatS S).card := Finset.card_pos.mpr ⟨x, hxmem⟩
    omega

/-- The unique positive point when posRatS has card 1. -/
theorem mem_posRatS_eq_of_card_one {S : Finset (P1Point ℚ)} {x α : ℚ}
    (hx : x ∈ posRatS S) (hα : α ∈ posRatS S) (hcard : (posRatS S).card = 1) :
    x = α := by
  have hle : (posRatS S).card ≤ 1 := by omega
  exact Finset.card_le_one.mp hle x hx α hα

/-- Base Good existence for |S| <= 3. -/
theorem baseGood_exists (S : Finset (P1Point ℚ)) (β : P1Point ℚ)
    (H : Lemma22Hypotheses S β) (hcard : S.card ≤ 3) :
    ∃ f : ℚ[X], Good f S β := by
  obtain ⟨b, hβ⟩ := beta_finite H
  obtain ⟨h0S, hinfS, hpos, hβnotin, hsep⟩ := H
  have hS2 : 2 ≤ S.card := by
    have hsub : ({P1Point.ofFinite (0:ℚ), P1Point.infty} : Finset (P1Point ℚ)) ⊆ S := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with h | h
      · rw [h]; exact h0S
      · rw [h]; exact hinfS
    have := Finset.card_le_card hsub
    have hc : ({P1Point.ofFinite (0:ℚ), P1Point.infty} : Finset (P1Point ℚ)).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp [P1Point.ofFinite, P1Point.infty]
    omega
  have hposcard : (posRatS S).card = S.card - 2 := posRatS_card S h0S hinfS
  have hble : (posRatS S).card ≤ 1 := by omega
  by_cases hz : (posRatS S).card = 0
  · -- no positive point: S = {0, infinity}, c = 2/b
    have hbne : b ≠ 0 := by
      intro hb0
      apply hβnotin
      rw [hβ, hb0]
      exact h0S
    let c : ℚ := 2 / b
    have hc : c ≠ 0 := by
      unfold c
      exact div_ne_zero (by norm_num) hbne
    have hcb : c * b = 2 := by
      unfold c
      field_simp
    have hzero : ∀ p ∈ S, p = P1Point.ofFinite (0:ℚ) ∨ p = P1Point.infty :=
      eq_zero_or_infty_of_pos_card_zero h0S hinfS hpos hz
    refine ⟨Polynomial.C c * Polynomial.X, ?_, ?_, ?_, ?_⟩
    · rw [Polynomial.natDegree_C_mul_X c hc]
    · intro p hp
      rcases hzero p hp with h | h
      · rw [h]
        simp [polyEvalP1, P1Point.ofFinite, specialSet]
      · rw [h]
        simp [polyEvalP1, P1Point.infty, specialSet]
    · show polyEvalP1 (Polynomial.C c * Polynomial.X) β ∉ specialSet ℚ
      rw [hβ]
      show P1Point.ofFinite ((Polynomial.C c * Polynomial.X).eval b) ∉ specialSet ℚ
      have hcbval : (Polynomial.C c * Polynomial.X).eval b = 2 := by
        simp [hcb]
      rw [hcbval]
      simp [RestatedLemma24InterfaceActual.specialSet, P1Point.ofFinite, P1Point.infty]
    · intro z _hz
      show Polynomial.aeval z (Polynomial.derivative (Polynomial.C c * Polynomial.X)) ≠ 0
      rw [Polynomial.derivative_C_mul_X, Polynomial.aeval_C]
      have hcC : ((c : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hc
      exact hcC
  · -- one positive point: S = {0, α, infinity}, c = alpha^{-1}
    have hone : (posRatS S).card = 1 := by omega
    obtain ⟨α, hαmem⟩ := Finset.card_pos.mp (by omega : 0 < (posRatS S).card)
    obtain ⟨pα, hpαS, hpα0, hpαinf, hpα⟩ := exists_of_mem_posRatS hαmem
    -- α > 0 from H positivity at pα
    have hαpos : 0 < α := by
      obtain ⟨x, hpx, hxpos⟩ := hpos pα hpαS hpα0 hpαinf
      have hpx' : P1Point.ofFinite α = P1Point.ofFinite x := by
        rw [← hpα]
        exact hpx
      have hαx : α = x := by simpa [P1Point.ofFinite] using hpx'
      rw [hαx]
      exact hxpos
    let c : ℚ := α⁻¹
    have hc : c ≠ 0 := by
      unfold c
      exact inv_ne_zero (ne_of_gt hαpos)
    have hcb : 2 ≤ c * b := by
      obtain ⟨a, b', hpa, hpb, h2⟩ := hsep (P1Point.ofFinite α) (by
        rw [← hpα]; exact hpαS)
        (by
          intro hh
          exact (ne_of_gt hαpos) (by simpa [P1Point.ofFinite] using hh))
        (P1Point.ofFinite_ne_infty α)
      have ha : a = α := by
        have hpa'' : P1Point.ofFinite α = P1Point.ofFinite a := hpa
        simpa [P1Point.ofFinite] using hpa''.symm
      have hb' : b' = b := by
        have : P1Point.ofFinite b' = P1Point.ofFinite b := by rw [← hpb, hβ]
        simpa [P1Point.ofFinite] using this
      rw [ha, hb'] at h2
      unfold c
      simpa [div_eq_mul_inv, mul_comm] using h2
    -- all points are 0, α or infinity
    have hclass : ∀ p ∈ S, p = P1Point.ofFinite (0:ℚ) ∨ p = P1Point.ofFinite α ∨
        p = P1Point.infty := by
      intro p hp
      by_cases h0 : p = P1Point.ofFinite (0:ℚ)
      · exact Or.inl h0
      by_cases hinf : p = P1Point.infty
      · exact Or.inr (Or.inr hinf)
      · right; left
        obtain ⟨x, hpx, hxpos⟩ := hpos p hp h0 hinf
        have hxmem : x ∈ posRatS S := mem_posRatS_of_mem hp h0 hinf hpx
        have hxα : x = α := mem_posRatS_eq_of_card_one hxmem hαmem hone
        rw [hpx, hxα]
    refine ⟨Polynomial.C c * Polynomial.X, ?_, ?_, ?_, ?_⟩
    · rw [Polynomial.natDegree_C_mul_X c hc]
    · intro p hp
      rcases hclass p hp with h | h | h
      · rw [h]
        simp [polyEvalP1, P1Point.ofFinite, specialSet]
      · rw [h]
        have hval : (Polynomial.C c * Polynomial.X).eval α = 1 := by
          unfold c
          simp [inv_mul_cancel₀ (ne_of_gt hαpos)]
        show P1Point.ofFinite ((Polynomial.C c * Polynomial.X).eval α) ∈ specialSet ℚ
        rw [hval]
        simp [RestatedLemma24InterfaceActual.specialSet, P1Point.ofFinite]
      · rw [h]
        show polyEvalP1 (Polynomial.C c * Polynomial.X) P1Point.infty ∈ specialSet ℚ
        simp [polyEvalP1, P1Point.infty, specialSet]
    · show polyEvalP1 (Polynomial.C c * Polynomial.X) β ∉ specialSet ℚ
      rw [hβ]
      show P1Point.ofFinite ((Polynomial.C c * Polynomial.X).eval b) ∉ specialSet ℚ
      have hcbval : (Polynomial.C c * Polynomial.X).eval b = c * b := by simp
      rw [hcbval]
      intro hmem
      simp only [RestatedLemma24InterfaceActual.specialSet, Set.mem_insert_iff,
        Set.mem_singleton_iff, P1Point.ofFinite, P1Point.infty, Option.some.injEq] at hmem
      rcases hmem with h | h | h
      · exact absurd h (by simp)
      · have h2le : 2 ≤ c * b := hcb
        linarith
      · have h2le : 2 ≤ c * b := hcb
        linarith
    · intro z _hz
      show Polynomial.aeval z (Polynomial.derivative (Polynomial.C c * Polynomial.X)) ≠ 0
      rw [Polynomial.derivative_C_mul_X, Polynomial.aeval_C]
      have hcC : ((c : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hc
      exact hcC

#check baseGood_exists

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22BaseGoodActual
end
