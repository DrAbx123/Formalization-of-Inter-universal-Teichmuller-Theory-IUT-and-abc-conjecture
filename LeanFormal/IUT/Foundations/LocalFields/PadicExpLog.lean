import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverseSharpRadius
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInjectivity
import Mathlib.Tactic

/-! # p-adic exp/log inverse on the principal-unit ball

Actual inverse pair between the p-adic analytic logarithm and a chosen
exponential on every closed ball of radius r < 1/2, built from
exists_log1p_preimage and log1p_injOn_closedBall.  The rational prime p is an
explicit parameter of every declaration.  No card. -/

noncomputable section

namespace LeanFormal.IUT.LocalFieldLogarithm

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K]

noncomputable def padicExp (p : ℕ) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r < 1 / 2)
    (y : K) (hy : ‖y‖ ≤ r) : K :=
  Classical.choose (exists_log1p_preimage (p := p) (K := K) hr hrhalf y hy)

theorem padicExp_spec (p : ℕ) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r < 1 / 2)
    (y : K) (hy : ‖y‖ ≤ r) :
    ‖padicExp (K := K) p r hr hrhalf y hy‖ ≤ r ∧
      log1p (padicExp (K := K) p r hr hrhalf y hy) = y :=
  Classical.choose_spec (exists_log1p_preimage (p := p) (K := K) hr hrhalf y hy)

theorem log1p_padicExp (p : ℕ) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r < 1 / 2)
    (y : K) (hy : ‖y‖ ≤ r) :
    log1p (padicExp (K := K) p r hr hrhalf y hy) = y :=
  (padicExp_spec (K := K) p r hr hrhalf y hy).2

theorem norm_log1p_le (p : ℕ) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r < 1 / 2)
    {x : K} (hx : ‖x‖ ≤ r) : ‖log1p x‖ ≤ r := by
  have hrem : ‖logRemainder x‖ ≤ r := by
    have h := norm_logRemainder_sub_le (p := p) (K := K) x (0 : K) hr
      (le_of_lt hrhalf) hx (by simpa using hr)
    have hzero : logRemainder (0 : K) = 0 := by simp [logRemainder, log1p_zero]
    rw [hzero, sub_zero, sub_zero] at h
    exact h.trans ((mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans hx)
  calc ‖log1p x‖ = ‖x + logRemainder x‖ := by
        rw [show log1p x = x + logRemainder x by
          unfold logRemainder
          ring]
    _ ≤ max ‖x‖ ‖logRemainder x‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ r := max_le hx hrem

theorem padicExp_log1p (p : ℕ) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r < 1 / 2)
    {x : K} (hx : ‖x‖ ≤ r) :
    padicExp (K := K) p r hr hrhalf (log1p x)
        (norm_log1p_le (K := K) p r hr hrhalf hx) = x := by
  apply log1p_injOn_closedBall (p := p) (K := K) hr hrhalf
    (padicExp_spec (K := K) p r hr hrhalf (log1p x)
      (norm_log1p_le (K := K) p r hr hrhalf hx)).1 hx
  exact log1p_padicExp (K := K) p r hr hrhalf (log1p x)
    (norm_log1p_le (K := K) p r hr hrhalf hx)

theorem padicExp_log_inverse (p : ℕ) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    (r : ℝ) (hr : 0 ≤ r) (hrhalf : r < 1 / 2)
    {x : K} (hx : ‖x‖ ≤ r) :
    padicExp (K := K) p r hr hrhalf (log1p x)
        (norm_log1p_le (K := K) p r hr hrhalf hx) = x ∧
      log1p (padicExp (K := K) p r hr hrhalf (log1p x)
        (norm_log1p_le (K := K) p r hr hrhalf hx)) = log1p x :=
  ⟨padicExp_log1p (K := K) p r hr hrhalf hx,
    log1p_padicExp (K := K) p r hr hrhalf (log1p x)
      (norm_log1p_le (K := K) p r hr hrhalf hx)⟩

end LeanFormal.IUT.LocalFieldLogarithm
end
