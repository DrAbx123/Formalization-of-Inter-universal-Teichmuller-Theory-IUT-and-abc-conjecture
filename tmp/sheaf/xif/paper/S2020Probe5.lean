import Mathlib.Tactic

lemma order_cases (n : ℕ) (h12 : 12 ∣ n) (hdvd : n ∣ 480)
    (hne12 : n ≠ 12) (hne60 : n ≠ 60) :
    n = 24 ∨ n = 48 ∨ n = 96 ∨ n = 120 ∨ n = 240 ∨ n = 480 := by
  rcases h12 with ⟨m, hm⟩
  have hm_dvd : m ∣ 40 := by
    have h : 12 * m ∣ 12 * 40 := by simpa [show 12 * 40 = 480 by norm_num] using (hm ▸ hdvd)
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 12)).mp h
  have hm_cases : m = 1 ∨ m = 2 ∨ m = 4 ∨ m = 5 ∨ m = 8 ∨ m = 10 ∨ m = 20 ∨ m = 40 := by
    have hm_le : m ≤ 40 := Nat.le_of_dvd (by norm_num) hm_dvd
    interval_cases m <;> norm_num at hm_dvd <;> omega
  rcases hm_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso; exact hne12 (by rw [hm])
  · left; rw [hm]
  · right; left; rw [hm]
  · exfalso; exact hne60 (by rw [hm])
  · right; right; left; rw [hm]
  · right; right; right; left; rw [hm]
  · right; right; right; right; left; rw [hm]
  · right; right; right; right; right; rw [hm]