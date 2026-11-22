import tmp.sheaf.xif.paper.Mzk1Lemma22ConditionedActual
import tmp.sheaf.xif.paper.Mzk1GChoiceUnramifiedActual
import tmp.sheaf.xif.paper.Mzk1GChoiceCardActual
import tmp.sheaf.xif.paper.Mzk1PolyUnramifiedCompositionActual
import tmp.sheaf.xif.paper.Mzk1PolyChainRuleActual
import tmp.sheaf.xif.paper.Mzk1Lemma22HypPreservationActual
import tmp.sheaf.xif.paper.Mzk1Lemma22HypPreservationSeparationActual
import tmp.sheaf.xif.paper.Mzk1GChoiceIntegrationActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22FullGateActual

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
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22CompositionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22InductionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceDataActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationSeparationActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22StatementShapeActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDataOfHypothesesActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22ConditionedActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyUnramifiedCompositionActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyChainRuleActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual

/-- Base case: FullShape for H-pairs with |S| <= 3 via linear polynomials. -/
theorem base_full (S : Finset (P1Point ℚ)) (β : P1Point ℚ)
    (H : Lemma22Hypotheses S β) (hcard : S.card ≤ 3) :
    Mzk1Lemma22FullShape S β := by
  obtain ⟨b, hβ⟩ := beta_finite H
  obtain ⟨h0S, hInfS, hpos, hβnotin, hsep⟩ := H
  by_cases hposmem : ∃ α : ℚ, P1Point.ofFinite α ∈ S ∧ 0 < α
  · obtain ⟨α, hαS, hαpos⟩ := hposmem
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have hsub : S ⊆ ({P1Point.ofFinite (0 : ℚ), P1Point.ofFinite α, P1Point.infty} :
        Finset (P1Point ℚ)) := by
      intro p hp
      by_cases h0 : p = P1Point.ofFinite (0 : ℚ)
      · simp [h0]
      by_cases hinf : p = P1Point.infty
      · simp [hinf]
      by_cases hα : p = P1Point.ofFinite α
      · simp [hα]
      · exfalso
        obtain ⟨x, hpx, hxpos⟩ := hpos p hp h0 hinf
        have hx0 : x ≠ 0 := by intro hx; apply h0; rw [hpx, hx]
        have hxα : x ≠ α := by intro hx; apply hα; rw [hpx, hx]
        have hαx : α ≠ x := fun h => hxα h.symm
        have hmem4 : ({P1Point.ofFinite (0 : ℚ), P1Point.ofFinite α,
            P1Point.ofFinite x, P1Point.infty} : Finset (P1Point ℚ)) ⊆ S := by
          intro q hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl
          · exact h0S
          · exact hαS
          · rw [← hpx]; exact hp
          · exact hInfS
        have h4card : ({P1Point.ofFinite (0 : ℚ), P1Point.ofFinite α,
            P1Point.ofFinite x, P1Point.infty} : Finset (P1Point ℚ)).card = 4 := by
          rw [Finset.card_eq_four]
          refine ⟨P1Point.ofFinite (0 : ℚ), P1Point.ofFinite α, P1Point.ofFinite x,
            P1Point.infty, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro h
            have h0a : (0 : ℚ) = α := by simpa [P1Point.ofFinite] using h
            exact hαne h0a.symm
          · intro h
            have h0x : (0 : ℚ) = x := by simpa [P1Point.ofFinite] using h
            exact hx0 h0x.symm
          · intro h; exact absurd h (by simp [P1Point.ofFinite, P1Point.infty])
          · intro h
            have hax : α = x := by simpa [P1Point.ofFinite] using h
            exact hαx hax
          · intro h; exact absurd h (by simp [P1Point.ofFinite, P1Point.infty])
          · intro h; exact absurd h (by simp [P1Point.ofFinite, P1Point.infty])
          · rfl
        have := Finset.card_le_card hmem4
        omega
    have hSetEq : S = ({P1Point.ofFinite (0 : ℚ), P1Point.ofFinite α, P1Point.infty} :
        Finset (P1Point ℚ)) := by
      apply Finset.eq_of_subset_of_card_le hsub
      have hmem3 : ({P1Point.ofFinite (0 : ℚ), P1Point.ofFinite α, P1Point.infty} :
          Finset (P1Point ℚ)) ⊆ S := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact h0S
        · exact hαS
        · exact hInfS
      have h3 : ({P1Point.ofFinite (0 : ℚ), P1Point.ofFinite α, P1Point.infty} :
          Finset (P1Point ℚ)).card = 3 := by
        rw [Finset.card_eq_three]
        refine ⟨P1Point.ofFinite (0 : ℚ), P1Point.ofFinite α, P1Point.infty,
          ?_, ?_, ?_, rfl⟩
        · intro h
          have h0a : (0 : ℚ) = α := by simpa [P1Point.ofFinite] using h
          exact hαne h0a.symm
        · intro h; exact absurd h (by simp [P1Point.ofFinite, P1Point.infty])
        · intro h; exact absurd h (by simp [P1Point.ofFinite, P1Point.infty])
      have := Finset.card_le_card hmem3
      omega
    let f : ℚ[X] := C α⁻¹ * X
    have hfdeg : 1 ≤ f.natDegree := by
      unfold f
      rw [natDegree_C_mul_X α⁻¹ (inv_ne_zero hαne)]
    have hvalα : f.eval α = 1 := by
      unfold f
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      exact inv_mul_cancel₀ hαne
    have hval0 : f.eval 0 = 0 := by
      unfold f
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero]
    refine ⟨f, hfdeg, ?_, ?_, ?_⟩
    · intro p hp
      rw [hSetEq] at hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h | h
      · rw [h]
        change some (f.eval 0) ∈ specialSet
        rw [hval0]
        exact zero_mem_specialSet
      · rw [h]
        change some (f.eval α) ∈ specialSet
        rw [hvalα]
        exact one_mem_specialSet
      · rw [h]
        exact infty_mem_specialSet
    · show polyMapPoints f β ∉ specialSet
      rw [hβ]
      change some (f.eval b) ∉ specialSet
      intro hmem
      simp only [specialSet, Set.mem_setOf_eq] at hmem
      rcases hmem with h | h | h
      · exact absurd h (by simp [P1Point.ofFinite, P1Point.infty])
      · -- f b = 0: b = 0, contradicts separation at alpha
        have h0 : f.eval b = 0 := by simpa [P1Point.ofFinite] using h
        have hb0 : b = 0 := by
          unfold f at h0
          simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at h0
          rcases mul_eq_zero.mp h0 with h | h
          · exact absurd h (inv_ne_zero hαne)
          · exact h
        obtain ⟨a, b', hpa, hpb, h2⟩ := hsep (P1Point.ofFinite α) hαS
          (by intro hh; exact hαne (by simpa [P1Point.ofFinite] using hh))
          (P1Point.ofFinite_ne_infty α)
        have hb' : b' = b := by
          have : P1Point.ofFinite b' = P1Point.ofFinite b := by rw [← hpb, hβ]
          simpa [P1Point.ofFinite] using this
        have ha : a = α := (by simpa [P1Point.ofFinite] using hpa).symm
        rw [ha, hb', hb0, zero_div] at h2
        linarith
      · have h1 : f.eval b = 1 := by simpa [P1Point.ofFinite] using h
        obtain ⟨a, b', hpa, hpb, h2⟩ := hsep (P1Point.ofFinite α) hαS
          (by intro hh; exact hαne (by simpa [P1Point.ofFinite] using hh))
          (P1Point.ofFinite_ne_infty α)
        have hb' : b' = b := by
          have : P1Point.ofFinite b' = P1Point.ofFinite b := by rw [← hpb, hβ]
          simpa [P1Point.ofFinite] using this
        have ha : a = α := (by simpa [P1Point.ofFinite] using hpa).symm
        rw [ha, hb'] at h2
        have hratio : b / α = 1 := by
          rw [div_eq_inv_mul]
          unfold f at h1
          simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using h1
        rw [hratio] at h2
        norm_num at h2
    · intro p hp
      cases p with
      | none =>
          show polyUnramifiedAt f (none : P1Point ℚ)
          simp only [polyUnramifiedAt]
          unfold f
          exact mul_ne_zero (Polynomial.C_ne_zero.mpr (inv_ne_zero hαne)) Polynomial.X_ne_zero
      | some x =>
          show polyUnramifiedAt f (P1Point.ofFinite x)
          simp only [polyUnramifiedAt]
          unfold f
          rw [Polynomial.derivative_C_mul_X]
          simpa [Polynomial.eval_C] using inv_ne_zero hαne
  · -- no positive point: S = {0, infinity}
    have hsub : S ⊆ ({P1Point.ofFinite (0 : ℚ), P1Point.infty} : Finset (P1Point ℚ)) := by
      intro p hp
      by_cases h0 : p = P1Point.ofFinite (0 : ℚ)
      · simp [h0]
      by_cases hinf : p = P1Point.infty
      · simp [hinf]
      · exfalso
        obtain ⟨x, hpx, hxpos⟩ := hpos p hp h0 hinf
        exact hposmem ⟨x, by rw [← hpx]; exact hp, hxpos⟩
    have hSetEq : S = ({P1Point.ofFinite (0 : ℚ), P1Point.infty} : Finset (P1Point ℚ)) := by
      apply Finset.eq_of_subset_of_card_le hsub
      have hmem2 : ({P1Point.ofFinite (0 : ℚ), P1Point.infty} : Finset (P1Point ℚ)) ⊆ S := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact h0S
        · exact hInfS
      have := Finset.card_le_card hmem2
      have h2c : ({P1Point.ofFinite (0 : ℚ), P1Point.infty} : Finset (P1Point ℚ)).card = 2 := by
        rw [Finset.card_insert_of_notMem, Finset.card_singleton]
        simp [P1Point.ofFinite, P1Point.infty]
      omega
    by_cases hb1 : b = 1
    · let f : ℚ[X] := C 2 * X
      have hfdeg : 1 ≤ f.natDegree := by
        unfold f
        rw [natDegree_C_mul_X 2 (by norm_num)]
      refine ⟨f, hfdeg, ?_, ?_, ?_⟩
      · intro p hp
        rw [hSetEq] at hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with h | h
        · rw [h]
          change some (f.eval 0) ∈ specialSet
          unfold f
          simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero]
          exact zero_mem_specialSet
        · rw [h]; exact infty_mem_specialSet
      · show polyMapPoints f β ∉ specialSet
        rw [hβ]
        change some (f.eval b) ∉ specialSet
        unfold f
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        rw [hb1]
        intro hmem
        simp only [specialSet, Set.mem_setOf_eq] at hmem
        rcases hmem with h | h | h
        · exact absurd h (by simp [P1Point.ofFinite, P1Point.infty])
        · have : (2 : ℚ) = 0 := by simpa [P1Point.ofFinite] using h
          norm_num at this
        · have : (2 : ℚ) = 1 := by simpa [P1Point.ofFinite] using h
          norm_num at this
      · intro p hp
        cases p with
        | none =>
            show polyUnramifiedAt f (none : P1Point ℚ)
            simp only [polyUnramifiedAt]
            unfold f
            exact mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num)) Polynomial.X_ne_zero
        | some x =>
            show polyUnramifiedAt f (P1Point.ofFinite x)
            simp only [polyUnramifiedAt]
            unfold f
            rw [Polynomial.derivative_C_mul_X]
            simpa [Polynomial.eval_C] using (show (2 : ℚ) ≠ 0 by norm_num)
    · let f : ℚ[X] := X
      have hfdeg : 1 ≤ f.natDegree := by
        unfold f; rw [Polynomial.natDegree_X]
      refine ⟨f, hfdeg, ?_, ?_, ?_⟩
      · intro p hp
        rw [hSetEq] at hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with h | h
        · rw [h]; exact zero_mem_specialSet
        · rw [h]; exact infty_mem_specialSet
      · show polyMapPoints f β ∉ specialSet
        rw [hβ]
        change some (f.eval b) ∉ specialSet
        unfold f
        simp only [Polynomial.eval_X]
        intro hmem
        simp only [specialSet, Set.mem_setOf_eq] at hmem
        rcases hmem with h | h | h
        · exact absurd h (by simp [P1Point.ofFinite, P1Point.infty])
        · have h0 : b = 0 := by simpa [P1Point.ofFinite] using h
          apply hβnotin; rw [hβ, h0]; exact h0S
        · have h1 : b = 1 := by simpa [P1Point.ofFinite] using h
          exact hb1 h1
      · intro p hp
        cases p with
        | none =>
            show polyUnramifiedAt f (none : P1Point ℚ)
            simp only [polyUnramifiedAt]
            unfold f
            exact Polynomial.X_ne_zero
        | some x =>
            show polyUnramifiedAt f (P1Point.ofFinite x)
            simp only [polyUnramifiedAt]
            unfold f
            rw [Polynomial.derivative_X]
            simp

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22FullGateActual
end
