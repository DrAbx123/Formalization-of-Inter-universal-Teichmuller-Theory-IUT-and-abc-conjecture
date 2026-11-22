import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
/-!
# P8-P (route §8.6): epsilon / delta / n selection

Route §8.6: given ε > 0, take δ = min 1 (ε/3), so (1+δ)^2 ≤ 1+ε; then choose
an integer n ≥ 4 with n/(n−3) ≤ 1+δ. These are fixed before Y_n, the finite map
family, K_V, η and all constants.
Lead lane: H-T / P8-P.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8EpsilonSelectionActual

/-- Route §8.6: δ = min 1 (ε/3) satisfies 0 < δ, δ ≤ 1 and (1+δ)^2 ≤ 1+ε. -/
theorem exists_delta_sq_le (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ (1 + δ) ^ 2 ≤ 1 + ε := by
  by_cases hε3 : ε ≤ 3
  · refine ⟨ε / 3, by positivity, by linarith, ?_⟩
    have hprod : 0 ≤ ε * (3 - ε) := mul_nonneg (le_of_lt hε) (by linarith)
    nlinarith
  · push_neg at hε3
    exact ⟨1, by norm_num, le_refl 1, by nlinarith⟩

/-- Route §8.6: for δ > 0 there is an integer n ≥ 4 with n/(n−3) ≤ 1+δ. -/
theorem exists_nat_ge_four_ratio_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, 4 ≤ n ∧ (n : ℝ) / ((n : ℝ) - 3) ≤ 1 + δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (3 / δ + 3)
  have h3n : (3 : ℝ) < (n : ℝ) := by
    have hpos : 0 < 3 / δ := by positivity
    linarith
  have hden : 0 < (n : ℝ) - 3 := by linarith
  have hn4 : 4 ≤ n := by
    have h3 : (3 : ℕ) < n := by exact_mod_cast h3n
    omega
  refine ⟨n, hn4, ?_⟩
  have h3le : 3 < δ * ((n : ℝ) - 3) := by
    have h : 3 / δ < (n : ℝ) - 3 := by linarith
    have := (div_lt_iff₀ hδ).mp h
    linarith [mul_comm ((n : ℝ) - 3) δ]
  rw [div_le_iff₀ hden]
  nlinarith

/-- Route §8.6 combined data. -/
theorem exists_epsilon_delta_nat (ε : ℝ) (hε : 0 < ε) :
    ∃ (δ : ℝ) (n : ℕ), 0 < δ ∧ δ ≤ 1 ∧ (1 + δ) ^ 2 ≤ 1 + ε ∧
      4 ≤ n ∧ (n : ℝ) / ((n : ℝ) - 3) ≤ 1 + δ := by
  obtain ⟨δ, hδ, hδ1, hδsq⟩ := exists_delta_sq_le ε hε
  obtain ⟨n, hn4, hnratio⟩ := exists_nat_ge_four_ratio_le δ hδ
  exact ⟨δ, n, hδ, hδ1, hδsq, hn4, hnratio⟩

end LeanFormal.IUT.XiFPaper.Mzk1P8EpsilonSelectionActual
