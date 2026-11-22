import Mathlib

namespace ProbeArith

theorem two_mul_div_two_of_odd {n : Nat} (hn : Odd n) :
    2 * ((n ^ 2 - 1) / 2) = n ^ 2 - 1 := by
  obtain ⟨m, hm⟩ := hn
  rw [hm]
  have h : (2 * m + 1) ^ 2 = 2 * (2 * m ^ 2 + 2 * m) + 1 := by ring
  rw [h, Nat.add_sub_cancel, Nat.mul_div_right]
  norm_num

theorem iff_of_two_mul {l b : Nat} (hodd : Odd l)
    (h : 1 + 2 * b = l ^ 2) : b = (l ^ 2 - 1) / 2 := by
  have htwo : 2 * ((l ^ 2 - 1) / 2) = l ^ 2 - 1 := two_mul_div_two_of_odd hodd
  have hb : 2 * b = l ^ 2 - 1 := by omega
  exact Nat.mul_left_cancel (by norm_num : 0 < 2) (hb.trans htwo.symm)

theorem iff_of_two_mul' {l b : Nat} (hodd : Odd l)
    (h : b = (l ^ 2 - 1) / 2) : 1 + 2 * b = l ^ 2 := by
  have htwo : 2 * ((l ^ 2 - 1) / 2) = l ^ 2 - 1 := two_mul_div_two_of_odd hodd
  have hl1 : 1 ≤ l ^ 2 := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm]
    nlinarith
  omega

end ProbeArith
