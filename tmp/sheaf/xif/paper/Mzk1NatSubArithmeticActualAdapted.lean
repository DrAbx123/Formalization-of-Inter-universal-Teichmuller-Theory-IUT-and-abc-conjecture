/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Section 0: natural subtraction/cancellation arithmetic -/

namespace LeanFormal.IUT.XiFPaper.NatSubArithmeticActual

variable {a b : Nat}

theorem add_sub_cancel' : a + b - b = a := Nat.add_sub_cancel a b

theorem add_sub_cancel_left' : b + a - b = a := Nat.add_sub_cancel_left b a

theorem sub_add_cancel' (h : b ≤ a) : a - b + b = a := Nat.sub_add_cancel h

theorem sub_le_self' : a - b ≤ a := Nat.sub_le a b

theorem sub_eq_zero_of_le' (h : a ≤ b) : a - b = 0 := Nat.sub_eq_zero_of_le h

theorem sub_self' : a - a = 0 := Nat.sub_self a

theorem zero_sub' : 0 - a = 0 := Nat.zero_sub a

theorem sub_le_sub_left' {c : Nat} (h : a ≤ b) : c - b ≤ c - a := 
  Nat.sub_le_sub_left h c

end LeanFormal.IUT.XiFPaper.NatSubArithmeticActual
