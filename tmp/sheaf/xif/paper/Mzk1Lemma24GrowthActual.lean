import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24GrowthActual

/-- **(M1a) Monic growth estimate for beta-avoidance** (paper [Mzk1] Lemma 2.4 lines
183-199): a monic polynomial of degree d >= 1 whose non-leading coefficients are bounded
by C grows like |z|^d, hence eventually exceeds any prescribed bound.  This is the formal
piece needed after the Lemma 2.3 normalization (beta large) and the (F) coefficient
bound (coeffs of f0 bounded by d0^d0): |f0(beta)| exceeds all values f0(alpha). -/
theorem s3135_monic_growth_of_coeff_bound
    (d : Nat) (hd : 1 ≤ d) (C B : Real) (hC : 0 ≤ C) :
    ∃ b : Real, B < b ∧ ∀ (p : Polynomial ℂ), p.Monic → p.natDegree = d →
      (∀ k, k < d → ‖p.coeff k‖ ≤ C) →
      ∀ z : ℂ, b + C * d ≤ ‖z‖ → b ≤ ‖p.eval z‖ := by
  refine ⟨max B 0 + 2, ?_, ?_⟩
  · have hB : B ≤ max B 0 := le_max_left _ _
    linarith
  · intro p hmon hdeg hcoeff z hz
    have hb0 : (0:ℝ) ≤ max B 0 := le_max_right _ _
    have hb1 : (1:ℝ) ≤ max B 0 + 2 := by linarith
    have hCd : (0:ℝ) ≤ C * d := mul_nonneg hC (Nat.cast_nonneg d)
    have hx1 : (1:ℝ) ≤ ‖z‖ :=
      le_trans hb1 (le_trans (le_add_of_nonneg_right hCd) hz)
    have hxpos : (0:ℝ) ≤ ‖z‖ := le_trans zero_le_one hx1
    have hcd : p.coeff d = 1 := by
      have h : p.leadingCoeff = 1 := hmon
      simpa [Polynomial.leadingCoeff, hdeg] using h
    have heval : p.eval z = z ^ d + ∑ k ∈ Finset.range d, p.coeff k * z ^ k := by
      rw [Polynomial.eval_eq_sum_range, hdeg, Finset.sum_range_succ, hcd, one_mul, add_comm]
    have hrest : ‖∑ k ∈ Finset.range d, p.coeff k * z ^ k‖ ≤ C * d * ‖z‖ ^ (d - 1) := by
      calc ‖∑ k ∈ Finset.range d, p.coeff k * z ^ k‖
          ≤ ∑ k ∈ Finset.range d, ‖p.coeff k * z ^ k‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range d, C * ‖z‖ ^ k := by
            apply Finset.sum_le_sum
            intro k hk
            have hklt : k < d := Finset.mem_range.mp hk
            have h1 : ‖p.coeff k * z ^ k‖ = ‖p.coeff k‖ * ‖z‖ ^ k := by
              rw [norm_mul, norm_pow]
            calc ‖p.coeff k * z ^ k‖ = ‖p.coeff k‖ * ‖z‖ ^ k := h1
              _ ≤ C * ‖z‖ ^ k :=
                  mul_le_mul_of_nonneg_right (hcoeff k hklt) (pow_nonneg hxpos k)
        _ = C * ∑ k ∈ Finset.range d, ‖z‖ ^ k := by rw [Finset.mul_sum]
        _ ≤ C * (d * ‖z‖ ^ (d - 1)) := by
            apply mul_le_mul_of_nonneg_left _ hC
            calc ∑ k ∈ Finset.range d, ‖z‖ ^ k
                ≤ ∑ k ∈ Finset.range d, ‖z‖ ^ (d - 1) := by
                  apply Finset.sum_le_sum
                  intro k hk
                  have hklt : k < d := Finset.mem_range.mp hk
                  exact pow_le_pow_right₀ hx1 (by omega)
              _ = d * ‖z‖ ^ (d - 1) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = C * d * ‖z‖ ^ (d - 1) := by ring
    have hlower : ‖z‖ ^ d - C * d * ‖z‖ ^ (d - 1) ≤ ‖p.eval z‖ := by
      rw [heval]
      have h := norm_sub_norm_le (z ^ d) (-∑ k ∈ Finset.range d, p.coeff k * z ^ k)
      simp only [norm_pow, norm_neg] at h
      calc ‖z‖ ^ d - C * d * ‖z‖ ^ (d - 1)
          ≤ ‖z‖ ^ d - ‖∑ k ∈ Finset.range d, p.coeff k * z ^ k‖ := by linarith
        _ ≤ ‖z ^ d + ∑ k ∈ Finset.range d, p.coeff k * z ^ k‖ := by
            simpa [sub_eq_add_neg] using h
    have hfac : ‖z‖ ^ d - C * (d:ℝ) * ‖z‖ ^ (d - 1) =
        ‖z‖ ^ (d - 1) * (‖z‖ - C * (d:ℝ)) := by
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 :=
        ⟨d - 1, (Nat.succ_pred_eq_of_pos (by omega : 0 < d)).symm⟩
      simp only [Nat.add_sub_cancel]
      rw [pow_succ]
      ring
    have hone : (1:ℝ) ≤ ‖z‖ ^ (d - 1) := one_le_pow₀ hx1
    have hxC : max B 0 + 2 ≤ ‖z‖ - C * d := by linarith
    have hpos : (0:ℝ) ≤ ‖z‖ - C * d := le_trans (by linarith : (0:ℝ) ≤ max B 0 + 2) hxC
    have hprod : max B 0 + 2 ≤ ‖z‖ ^ (d - 1) * (‖z‖ - C * d) := by
      calc max B 0 + 2 = 1 * (max B 0 + 2) := by ring
        _ ≤ ‖z‖ ^ (d - 1) * (‖z‖ - C * d) :=
            mul_le_mul hone hxC (by linarith) (le_trans zero_le_one hone)
    calc max B 0 + 2 ≤ ‖z‖ ^ (d - 1) * (‖z‖ - C * d) := hprod
      _ = ‖z‖ ^ d - C * d * ‖z‖ ^ (d - 1) := hfac.symm
      _ ≤ ‖p.eval z‖ := hlower

#check s3135_monic_growth_of_coeff_bound
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24GrowthActual
end