import Mathlib
import tmp.sheaf.xif.paper.Mzk1Lemma23Actual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma23NormalizationActual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma23Actual

/-- The normalization map f(x) = t / (x - lam) from [Mzk1] Lemma 2.3, scaled by t. -/
def normMap (S : Finset ℂ) (β : ℂ) (C : ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  (t : ℂ) * (1 / (z - lam S β C))

/-- The distance from beta to lam is eps. -/
theorem s3135_dist_beta_lam (S : Finset ℂ) (β : ℂ) (C : ℝ) (hβ : β ∉ S) (hC : 0 < C) :
    dist β (lam S β C) = eps S β C := by
  unfold lam
  rw [dist_eq_norm]
  have h : β - (β + (eps S β C : ℂ)) = (-(eps S β C) : ℂ) := by ring
  rw [h, norm_neg]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (eps_pos S β C hβ hC)]

/-- Every alpha in S is different from lam. -/
theorem s3135_alpha_ne_lam (S : Finset ℂ) (β : ℂ) (C : ℝ) (hβ : β ∉ S) (hC : 0 < C)
    {α : ℂ} (hα : α ∈ S) : α ≠ lam S β C := by
  have hd : 0 < dist α (lam S β C) := by
    have := dist_alpha_lam_ge S β C hβ hC hα
    have hce : 0 < C * eps S β C := mul_pos hC (eps_pos S β C hβ hC)
    linarith
  intro h
  rw [h, dist_self] at hd
  exact lt_irrefl 0 hd

/-- Value bound: |f(alpha)| <= 1/(C*eps) for alpha in S. -/
theorem s3135_norm_f_alpha_le (S : Finset ℂ) (β : ℂ) (C : ℝ) (hβ : β ∉ S) (hC : 0 < C)
    {α : ℂ} (hα : α ∈ S) : ‖1 / (α - lam S β C)‖ ≤ 1 / (C * eps S β C) := by
  have hce : 0 < C * eps S β C := mul_pos hC (eps_pos S β C hβ hC)
  have hd : C * eps S β C ≤ dist α (lam S β C) := dist_alpha_lam_ge S β C hβ hC hα
  have hnorm : ‖α - lam S β C‖ = dist α (lam S β C) := by
    rw [dist_eq_norm]
  rw [norm_div, norm_one, hnorm]
  exact one_div_le_one_div_of_le hce hd

/-- Value at beta: |f(beta)| = 1/eps. -/
theorem s3135_norm_f_beta (S : Finset ℂ) (β : ℂ) (C : ℝ) (hβ : β ∉ S) (hC : 0 < C) :
    ‖1 / (β - lam S β C)‖ = 1 / eps S β C := by
  have he : 0 < eps S β C := eps_pos S β C hβ hC
  have hd : ‖β - lam S β C‖ = eps S β C := by
    rw [← dist_eq_norm]
    exact s3135_dist_beta_lam S β C hβ hC
  rw [norm_div, norm_one, hd]

/-- **Lemma 2.3 normalization (existence)**: for a finite set S, beta outside S, and any
bound B >= 1, there is a scaling t > 0 such that f(x) = t/(x - lam) maps every alpha in
S into the closed unit disk and beta to a point of norm at least B.  (Paper [Mzk1]
Lemma 2.4 lines 163-169: the affine normalization making |alpha| <= 1 and |beta| large.) -/
theorem s3135_normalization_exists (S : Finset ℂ) (β : ℂ) (hβ : β ∉ S)
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ t : ℝ, 0 < t ∧
      (∀ α ∈ S, ‖normMap S β B t α‖ ≤ 1) ∧
      B ≤ ‖normMap S β B t β‖ := by
  classical
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have he : 0 < eps S β B := eps_pos S β B hβ hB0
  have hce : 0 < B * eps S β B := mul_pos hB0 he
  by_cases hS : S.Nonempty
  · -- nonempty: t = 1 / max |f(alpha)|
    let vals : Finset ℝ := S.image (fun α => ‖1 / (α - lam S β B)‖)
    have hvals : vals.Nonempty := hS.image _
    let M : ℝ := vals.max' hvals
    have hMpos : 0 < M := by
      obtain ⟨α, hα, hMα⟩ := Finset.mem_image.mp (Finset.max'_mem vals hvals)
      have hpos : 0 < ‖1 / (α - lam S β B)‖ := by
        apply norm_pos_iff.mpr
        exact div_ne_zero one_ne_zero (sub_ne_zero.mpr (s3135_alpha_ne_lam S β B hβ hB0 hα))
      change 0 < vals.max' hvals
      rw [← hMα]
      exact hpos
    have hMne : M ≠ 0 := hMpos.ne'
    refine ⟨1 / M, div_pos one_pos hMpos, ?_, ?_⟩
    · intro α hα
      have hle : ‖1 / (α - lam S β B)‖ ≤ M := by
        have : ‖1 / (α - lam S β B)‖ ∈ vals := Finset.mem_image_of_mem _ hα
        exact Finset.le_max' vals _ this
      have hbound := s3135_norm_f_alpha_le S β B hβ hB0 hα
      have hbalpha : ‖1 / (α - lam S β B)‖ ≤ 1 / (B * eps S β B) := hbound
      show ‖normMap S β B (1 / M) α‖ ≤ 1
      unfold normMap
      rw [norm_mul]
      have ht : ‖((1 / M : ℝ) : ℂ)‖ = 1 / M := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos one_pos hMpos)]
      rw [ht]
      calc (1 / M) * ‖1 / (α - lam S β B)‖ ≤ (1 / M) * M := by
            exact mul_le_mul_of_nonneg_left hle (le_of_lt (div_pos one_pos hMpos))
        _ = 1 := by rw [one_div, inv_mul_cancel₀ hMne]
    · have hle : ‖1 / (β - lam S β B)‖ = 1 / eps S β B := s3135_norm_f_beta S β B hβ hB0
      have hMle : M ≤ 1 / (B * eps S β B) := by
        obtain ⟨α, hα, hMα⟩ := Finset.mem_image.mp (Finset.max'_mem vals hvals)
        change vals.max' hvals ≤ 1 / (B * eps S β B)
        rw [← hMα]
        exact s3135_norm_f_alpha_le S β B hβ hB0 hα
      show B ≤ ‖normMap S β B (1 / M) β‖
      unfold normMap
      rw [norm_mul]
      have ht : ‖((1 / M : ℝ) : ℂ)‖ = 1 / M := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos one_pos hMpos)]
      rw [ht, hle]
      have hMle' : M ≤ 1 / (B * eps S β B) := hMle
      have h1 : M * (B * eps S β B) ≤ 1 := by
        have hpos2 : 0 < B * eps S β B := hce
        rw [le_div_iff₀ hpos2] at hMle'
        linarith
      have heps : (1 / M) * (1 / eps S β B) = (1 / eps S β B) / M := by ring
      rw [heps]
      have htarget : (1 / eps S β B) / M = (1 / eps S β B) / M := rfl
      rw [htarget]
      rw [le_div_iff₀ hMpos]
      calc B * M ≤ B * (1 / (B * eps S β B)) := by
            exact mul_le_mul_of_nonneg_left hMle (le_of_lt hB0)
        _ = 1 / eps S β B := by
            have hBne : (B:ℝ) ≠ 0 := hB0.ne'
            have hene : eps S β B ≠ 0 := he.ne'
            field_simp [hBne, hene]
  · -- empty: choose t = B * eps
    refine ⟨B * eps S β B, by positivity, ?_, ?_⟩
    · intro α hα
      exact absurd hα (Finset.not_nonempty_iff_eq_empty.mp hS ▸ by simp)
    · show B ≤ ‖normMap S β B (B * eps S β B) β‖
      unfold normMap
      rw [norm_mul, s3135_norm_f_beta S β B hβ hB0]
      have ht : ‖((B * eps S β B : ℝ) : ℂ)‖ = B * eps S β B := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [ht]
      have : (B * eps S β B) * (1 / eps S β B) = B := by
        have hene : eps S β B ≠ 0 := he.ne'
        field_simp [hene]
      rw [this]

#check s3135_normalization_exists
end LeanFormal.IUT.XiFPaper.Mzk1Lemma23NormalizationActual
end