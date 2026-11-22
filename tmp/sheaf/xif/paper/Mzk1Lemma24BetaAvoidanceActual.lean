import Mathlib
import tmp.sheaf.xif.paper.Mzk1Lemma24GrowthActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24BetaAvoidanceActual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma24GrowthActual

/-- Value bound on the unit disk for a polynomial with bounded coefficients (paper
[Mzk1] Lemma 2.4 lines 187-199: the values f0(alpha) at alpha in S are bounded by a
fixed expression in d0). -/
theorem s3135_poly_value_bound (d : Nat) (C : Real) (hC1 : 1 ≤ C)
    (p : Polynomial ℂ) (hdeg : p.natDegree ≤ d)
    (hcoeff : ∀ k, ‖p.coeff k‖ ≤ C) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖p.eval z‖ ≤ C * (d + 1) := by
  rw [Polynomial.eval_eq_sum_range]
  calc ‖∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * z ^ k‖
      ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k * z ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1), C := by
        apply Finset.sum_le_sum
        intro k hk
        have h1 : ‖p.coeff k * z ^ k‖ = ‖p.coeff k‖ * ‖z‖ ^ k := by
          rw [norm_mul, norm_pow]
        have h2 : ‖z‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
        calc ‖p.coeff k * z ^ k‖ = ‖p.coeff k‖ * ‖z‖ ^ k := h1
          _ ≤ C * 1 := mul_le_mul (hcoeff k) h2 (pow_nonneg (norm_nonneg z) k)
              (le_trans zero_le_one hC1)
          _ = C := by ring
    _ = C * ((p.natDegree : Real) + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ C * (d + 1) := by
        apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hC1)
        have : (p.natDegree : Real) ≤ d := by exact_mod_cast hdeg
        linarith

/-- **(M1b) Beta-avoidance from normalization + growth + coefficient bound** (paper
[Mzk1] Lemma 2.4 lines 183-199): if f0 is monic of degree d0 with non-leading
coefficients bounded by C (the (F) coefficient bound d0^d0) and alpha is normalized by
|alpha| <= 1, then beta with |beta| large enough satisfies f0(beta) != f0(alpha).
Thus after the Lemma 2.3 normalization, beta avoids S' = f0(S) in the Lemma 2.4
induction step. -/
theorem s3135_beta_avoidance (d : Nat) (hd : 1 ≤ d) (C : Real) (hC1 : 1 ≤ C) :
    ∃ b : Real, ∀ (p : Polynomial ℂ), p.Monic → p.natDegree = d →
      (∀ k, k < d → ‖p.coeff k‖ ≤ C) →
      ∀ α β : ℂ, ‖α‖ ≤ 1 → b + C * d ≤ ‖β‖ → p.eval β ≠ p.eval α := by
  obtain ⟨b, hb, hgrowth⟩ :=
    s3135_monic_growth_of_coeff_bound d hd C (C * (d + 1)) (le_trans zero_le_one hC1)
  refine ⟨b, ?_⟩
  intro p hmon hdeg hcoeff α β hα hβ heq
  have hbound : ‖p.eval α‖ ≤ C * (d + 1) := by
    apply s3135_poly_value_bound d C hC1 p
    · rw [hdeg]
    · intro k
      by_cases hk : k < d
      · exact le_trans (hcoeff k hk) (le_refl C)
      · have hkd : d ≤ k := by omega
        by_cases hkd' : k = d
        · have hcd : p.coeff d = 1 := by
            have h : p.leadingCoeff = 1 := hmon
            simpa [Polynomial.leadingCoeff, hdeg] using h
          rw [hkd', hcd, norm_one]
          exact hC1
        · have hkgt : d < k := lt_of_le_of_ne hkd (fun h => hkd' h.symm)
          have hzero : p.coeff k = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            rw [hdeg]; exact hkgt
          rw [hzero, norm_zero]
          linarith
    · exact hα
  have hlow : b ≤ ‖p.eval β‖ := by
    exact hgrowth p hmon hdeg hcoeff β hβ
  have hcontr : ‖p.eval β‖ ≤ C * (d + 1) := by
    rw [heq]; exact hbound
  linarith

#check s3135_poly_value_bound
#check s3135_beta_avoidance
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24BetaAvoidanceActual
end