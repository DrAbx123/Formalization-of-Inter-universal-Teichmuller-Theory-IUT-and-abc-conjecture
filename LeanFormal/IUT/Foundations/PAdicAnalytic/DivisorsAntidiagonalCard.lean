import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

namespace Nat

/-- The number of ordered positive factor pairs of a nonzero natural number is
at most the number itself. -/
theorem card_divisorsAntidiagonal_le (n : ℕ) :
    (Nat.divisorsAntidiagonal n).card ≤ n := by
  by_cases hn : n = 0
  · subst hn
    simp [Nat.divisorsAntidiagonal]
  · have hsubset : (Nat.divisorsAntidiagonal n).image (fun x : ℕ × ℕ => x.1) ⊆ n.divisors := by
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨x, hx, rfl⟩
      have hx' := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have hxpos : x.1 ≠ 0 := by
        intro h0
        apply hn
        rw [← hx', h0, Nat.zero_mul]
      rw [Nat.mem_divisors]
      exact ⟨hx'.symm ▸ dvd_mul_right x.1 x.2, hn⟩
    have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1) ↑(Nat.divisorsAntidiagonal n) := by
      intro x hx y hy hxy
      have hx' := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have hy' := (Nat.mem_divisorsAntidiagonal.mp hy).1
      have hxpos : x.1 ≠ 0 := by
        intro h0
        apply hn
        rw [← hx', h0, Nat.zero_mul]
      ext
      · exact hxy
      · have hmul : x.1 * x.2 = y.1 * y.2 := by rw [hx', hy']
        have hxy' : x.1 = y.1 := hxy
        rw [← hxy'] at hmul
        exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hxpos) hmul
    calc
      (Nat.divisorsAntidiagonal n).card = ((Nat.divisorsAntidiagonal n).image (fun x : ℕ × ℕ => x.1)).card := by
        rw [Finset.card_image_of_injOn hinj]
      _ ≤ n.divisors.card := Finset.card_le_card hsubset
      _ ≤ n := Nat.card_divisors_le_self n

end Nat
