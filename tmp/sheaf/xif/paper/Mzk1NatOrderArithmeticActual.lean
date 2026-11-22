/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Section 0: natural-order arithmetic wrappers -/

namespace LeanFormal.IUT.XiFPaper.NatOrderArithmeticActual

variable {a b c : Nat}

theorem zero_le' (a : Nat) : 0 ≤ a := Nat.zero_le a

theorem le_add_right' (a b : Nat) : a ≤ a + b := Nat.le_add_right a b

theorem le_add_left' (a b : Nat) : a ≤ b + a := Nat.le_add_left a b

theorem le_trans' (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := Nat.le_trans h1 h2

theorem lt_of_lt_of_le' (h1 : a < b) (h2 : b ≤ c) : a < c :=
  Nat.lt_of_lt_of_le h1 h2

theorem le_of_lt' (h : a < b) : a ≤ b := Nat.le_of_lt h

theorem add_le_add' (h1 : a ≤ b) (h2 : c ≤ b) : a + c ≤ b + b := 
  Nat.add_le_add h1 h2

theorem add_lt_add' (h1 : a < b) (h2 : c < b) : a + c < b + b := 
  Nat.add_lt_add h1 h2

theorem add_le_add_right' (h : a ≤ b) (c : Nat) : a + c ≤ b + c :=
  Nat.add_le_add_right h c

theorem add_lt_add_right' (h : a < b) (c : Nat) : a + c < b + c :=
  Nat.add_lt_add_right h c

end LeanFormal.IUT.XiFPaper.NatOrderArithmeticActual
