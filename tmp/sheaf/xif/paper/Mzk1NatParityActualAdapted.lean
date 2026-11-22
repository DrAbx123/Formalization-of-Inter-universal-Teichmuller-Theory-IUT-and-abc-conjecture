/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Log-shell: parity arithmetic for p and p* case analysis -/

namespace LeanFormal.IUT.XiFPaper.NatParityActual

theorem nat_mod_two_eq_zero_or_one (p : Nat) : p % 2 = 0 ∨ p % 2 = 1 :=
  Nat.mod_two_eq_zero_or_one p

theorem odd_eq_two_mul_add_one {p : Nat} (hp : p % 2 = 1) : ∃ k : Nat, p = 2 * k + 1 := by
  refine ⟨p / 2, ?_⟩
  have h := Nat.div_add_mod p 2
  rw [hp] at h
  omega

theorem even_eq_two_mul {p : Nat} (hp : p % 2 = 0) : ∃ k : Nat, p = 2 * k := by
  refine ⟨p / 2, ?_⟩
  have h := Nat.div_add_mod p 2
  rw [hp] at h
  omega

theorem mod_two_ne_one_iff_even {p : Nat} : p % 2 ≠ 1 ↔ p % 2 = 0 := by
  rcases nat_mod_two_eq_zero_or_one p with h | h
  · simp [h]
  · simp [h]

theorem mod_two_eq_one_or_even (p : Nat) : p % 2 = 1 ∨ p % 2 = 0 := by
  rcases nat_mod_two_eq_zero_or_one p with h | h
  · exact Or.inr h
  · exact Or.inl h

end LeanFormal.IUT.XiFPaper.NatParityActual
