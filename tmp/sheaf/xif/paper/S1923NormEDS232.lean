import Mathlib.NumberTheory.EllipticDivisibilitySequence

lemma normEDS_two_three_two_nat (n : ℕ) : normEDS (2 : ℤ) 3 2 (n : ℤ) = n := by
  induction n using normEDSRec with
  | zero => simp
  | one => simp
  | two => simp
  | three => simp
  | four => simp
  | even m h1 h2 h3 h4 h5 =>
    have h := normEDS_even (b := (2 : ℤ)) (c := 3) (d := 2) (m + 3)
    rw [show (↑m : ℤ) + 3 - 1 = (↑m : ℤ) + 2 by ring,
      show (↑m : ℤ) + 3 + 2 = (↑m : ℤ) + 5 by ring,
      show (↑m : ℤ) + 3 - 2 = (↑m : ℤ) + 1 by ring,
      show (↑m : ℤ) + 3 + 1 = (↑m : ℤ) + 4 by ring] at h
    norm_num at h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4, h5] at h
    rw [show ((2 * (m + 3) : ℕ) : ℤ) = 2 * ((m : ℤ) + 3) by push_cast; ring]
    have h' : normEDS (2 : ℤ) 3 2 (2 * ((m : ℤ) + 3)) * 2 = (2 * ((m : ℤ) + 3)) * 2 := by
      rw [h]; ring
    exact mul_right_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h'
  | odd m h1 h2 h3 h4 =>
    have h := normEDS_odd (b := (2 : ℤ)) (c := 3) (d := 2) (m + 2)
    rw [show (↑m : ℤ) + 2 + 2 = (↑m : ℤ) + 4 by ring,
      show (↑m : ℤ) + 2 - 1 = (↑m : ℤ) + 1 by ring,
      show (↑m : ℤ) + 2 + 1 = (↑m : ℤ) + 3 by ring] at h
    norm_num at h1 h2 h3 h4
    rw [h1, h2, h3, h4] at h
    rw [show ((2 * (m + 2) + 1 : ℕ) : ℤ) = 2 * ((m : ℤ) + 2) + 1 by push_cast; ring]
    rw [h]
    ring

lemma normEDS_two_three_two (n : ℤ) : normEDS (2 : ℤ) 3 2 n = n := by
  induction n using Int.negInduction with
  | nat n => exact normEDS_two_three_two_nat n
  | neg ih n =>
    rw [show (-(n : ℤ)) = -((n : ℤ)) by ring, normEDS_neg, normEDS_two_three_two_nat n]
