
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Normed.Field.Basic

noncomputable section

namespace S2223Probe

variable {K : Type*} [Field K]

theorem sqrt_of_odd_zpow (q : K) (hq : q ≠ 0) (x : Kˣ) (m : ℤ)
    (hx : (x : K) ^ 2 = q ^ m) (hm : Odd m) :
    ∃ s : K, s ^ 2 = q := by
  obtain ⟨k, hk⟩ := hm
  have hqm : q ^ m = q * (q ^ k) ^ 2 := by
    rw [hk]
    rw [show (2 : ℤ) * k + 1 = 1 + k * 2 by ring]
    rw [zpow_add₀ hq]
    rw [show (q ^ k) ^ 2 = q ^ (k * 2) by
      rw [← zpow_natCast, ← zpow_mul]
      norm_num]
    rw [zpow_one, mul_comm]
  refine ⟨(x : K) / q ^ k, ?_⟩
  rw [div_pow, hx, hqm]
  field_simp [hq]

end S2223Probe
end
