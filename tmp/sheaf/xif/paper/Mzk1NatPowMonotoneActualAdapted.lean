/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Log-shell: natural-power monotonicity laws -/

namespace LeanFormal.IUT.XiFPaper.NatPowMonotoneActual

theorem pow_le_pow_right' {p : Nat} (hp : 1 ≤ p) {m n : Nat} (h : m ≤ n) :
    p ^ m ≤ p ^ n := Nat.pow_le_pow_right hp h

theorem pow_lt_pow_right' {p : Nat} (hp : 1 < p) {m n : Nat} (h : m < n) :
    p ^ m < p ^ n := Nat.pow_lt_pow_right hp h

theorem pow_pos' {p : Nat} (hp : 0 < p) (n : Nat) : 0 < p ^ n := Nat.pow_pos hp n

theorem pow_succ_pos {p : Nat} (hp : 0 < p) (n : Nat) : 0 < p ^ (n + 1) :=
  Nat.pow_pos hp (n + 1)

theorem pow_ne_zero' {p : Nat} (hp : 0 < p) (n : Nat) : p ^ n ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (Nat.pow_pos hp n)

theorem one_pow' (n : Nat) : (1 : Nat) ^ n = 1 := one_pow n

theorem pow_zero' (p : Nat) : p ^ 0 = 1 := pow_zero p

end LeanFormal.IUT.XiFPaper.NatPowMonotoneActual
