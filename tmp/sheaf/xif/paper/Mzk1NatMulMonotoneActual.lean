/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips: natural multiplication monotonicity -/

namespace LeanFormal.IUT.XiFPaper.NatMulMonotoneActual

theorem nat_mul_le_mul' {a b c d : Nat} (h1 : a ≤ b) (h2 : c ≤ d) :
    a * c ≤ b * d := Nat.mul_le_mul h1 h2

theorem nat_mul_le_mul_right' {a b c : Nat} (h : a ≤ b) : a * c ≤ b * c :=
  Nat.mul_le_mul_right c h

theorem nat_mul_le_mul_left' {a b c : Nat} (h : a ≤ b) : c * a ≤ c * b :=
  Nat.mul_le_mul_left c h

theorem nat_mul_lt_mul_of_pos_right' {a b c : Nat} (h : a < b) (hc : 0 < c) :
    a * c < b * c := Nat.mul_lt_mul_of_pos_right h hc

theorem nat_mul_lt_mul_of_pos_left' {a b c : Nat} (h : a < b) (hc : 0 < c) :
    c * a < c * b := Nat.mul_lt_mul_of_pos_left h hc

theorem nat_mul_pos' {a b : Nat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  Nat.mul_pos ha hb

theorem nat_mul_eq_zero_iff' {a b : Nat} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  Nat.mul_eq_zero

end LeanFormal.IUT.XiFPaper.NatMulMonotoneActual
