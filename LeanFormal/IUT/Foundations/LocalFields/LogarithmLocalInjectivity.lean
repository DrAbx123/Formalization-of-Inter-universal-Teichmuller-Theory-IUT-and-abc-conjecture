import LeanFormal.IUT.Foundations.LocalFields.LogarithmRemainder

namespace LeanFormal.IUT.LocalFieldLogarithm

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]

include p

/-- The logarithm is injective on every closed ball of radius less than one half. -/
theorem log1p_injOn_closedBall {r : ℝ} (hr : 0 ≤ r) (hrhalf : r < 1 / 2) :
    Set.InjOn (log1p : K → K) {x | ‖x‖ ≤ r} := by
  intro x hx y hy hlog
  have hremainder : logRemainder x - logRemainder y = -(x - y) := by
    dsimp [logRemainder]
    rw [hlog]
    ring
  have hbound := norm_logRemainder_sub_le (p := p) x y hr (le_of_lt hrhalf) hx hy
  rw [hremainder, norm_neg] at hbound
  have hnorm : ‖x - y‖ = 0 := by
    by_contra hnonzero
    have hpositive : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnonzero)
    have hcoefficient : 2 * r < 1 := by linarith
    have hstrict := mul_lt_mul_of_pos_right hcoefficient hpositive
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- In a closed ball of radius less than one half, the logarithm vanishes only at zero. -/
theorem log1p_eq_zero_iff_of_norm_le {r : ℝ} (hr : 0 ≤ r) (hrhalf : r < 1 / 2)
    {x : K} (hx : ‖x‖ ≤ r) : log1p x = 0 ↔ x = 0 := by
  constructor
  · intro hlog
    apply log1p_injOn_closedBall (p := p) hr hrhalf hx
      (show ‖(0 : K)‖ ≤ r by simpa using hr)
    simpa only [log1p_zero] using hlog
  · rintro rfl
    exact log1p_zero

end LeanFormal.IUT.LocalFieldLogarithm
