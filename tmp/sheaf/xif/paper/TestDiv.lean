import Mathlib

lemma test_div (n : ℤ) : 12 ∣ 5 * n^3 + 7 * n^5 := by
  have h : ((5 * n^3 + 7 * n^5 : ℤ) : ZMod 12) = 0 := by
    push_cast
    have hall : ∀ x : ZMod 12, 5 * x^3 + 7 * x^5 = 0 := by decide
    exact hall (n : ZMod 12)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
