/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A766: shell arithmetic identities -/

/- (1) `sFactor` identity with lana indexing: `sFactor n = (sum_{j<n} (j+1)^2)/n`, so
`sum_{j<n} ((j+1)^2 - 1) = n*(sFactor n - 1)`, equivalently
`(1/n)*sum_{j<n} ((j+1)^2 - 1) = sFactor n - 1` for n > 0 (PROVED below).
(2) shell volume coefficient arithmetic: for the Q_p(zeta_p) model, e = p-1, r = 1,
n = p-1 gives `1 - 1/e - r/n = (p-3)/(p-1)` (PROVED). -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual

def sFactor (n : ℕ) : ℝ := (∑ j ∈ Finset.range n, ((j : ℝ) + 1) ^ 2) / (n : ℝ)

theorem shell_sum_identity (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2 - 1)) = (n : ℝ) * (sFactor n - 1) := by
  have hsum : (∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2 - 1))
      = (∑ j ∈ Finset.range n, ((j : ℝ) + 1) ^ 2) - (n : ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp
  unfold sFactor
  rw [hsum]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  field_simp [hnR]

theorem shell_average_identity (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * (∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2 - 1)) = sFactor n - 1 := by
  rw [shell_sum_identity n hn]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  field_simp [hnR]

theorem shell_coeff_QpZetap (p : ℝ) (hp : p ≠ 1) :
    1 - 1 / (p - 1) - 1 / (p - 1) = (p - 3) / (p - 1) := by
  have h : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp
  field_simp [h]
  ring

/-- Numeric instance `p = 5`: coefficient `(5-3)/(5-1) = 1/2`. -/
theorem shell_coeff_p5 : 1 - 1 / (4 : ℝ) - 1 / 4 = 1 / 2 := by norm_num

end LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
