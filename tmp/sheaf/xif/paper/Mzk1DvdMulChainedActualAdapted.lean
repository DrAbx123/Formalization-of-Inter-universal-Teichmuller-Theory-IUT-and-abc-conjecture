/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips: chained divisibility under multiplication -/

namespace LeanFormal.IUT.XiFPaper.DvdMulChainedActual

variable {a b c d : Nat}

theorem dvd_mul_right_of_dvd' (h : a ∣ b) (c : Nat) : a * c ∣ b * c := by
  rcases h with ⟨k, rfl⟩
  exact ⟨k, by ring⟩

theorem dvd_mul_left_of_dvd' (h : a ∣ b) (c : Nat) : c * a ∣ c * b := by
  rcases h with ⟨k, rfl⟩
  exact ⟨k, by ring⟩

theorem dvd_mul_of_dvd_mul' (h1 : a ∣ b) (h2 : c ∣ d) : a * c ∣ b * d := by
  rcases h1 with ⟨k, rfl⟩
  rcases h2 with ⟨l, rfl⟩
  exact ⟨k * l, by ring⟩

theorem dvd_mul_of_dvd_of_dvd' (h1 : a ∣ b) (h2 : c ∣ d) : a * c ∣ b * d :=
  dvd_mul_of_dvd_mul' h1 h2

theorem dvd_pow_of_dvd' (h : a ∣ b) (n : Nat) : a ^ n ∣ b ^ n := by
  rcases h with ⟨k, rfl⟩
  induction n with
  | zero =>
      simp
  | succ m ih =>
      rw [pow_succ, pow_succ]
      exact dvd_mul_of_dvd_mul' ih (dvd_refl (a * k))

end LeanFormal.IUT.XiFPaper.DvdMulChainedActual
