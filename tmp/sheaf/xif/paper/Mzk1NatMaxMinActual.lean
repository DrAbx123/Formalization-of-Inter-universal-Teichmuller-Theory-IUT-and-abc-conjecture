/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Section 0: natural max/min arithmetic wrappers -/

namespace LeanFormal.IUT.XiFPaper.NatMaxMinActual

theorem le_max_left' (a b : Nat) : a ≤ max a b := Nat.le_max_left a b

theorem le_max_right' (a b : Nat) : b ≤ max a b := Nat.le_max_right a b

theorem min_le_left' (a b : Nat) : min a b ≤ a := Nat.min_le_left a b

theorem min_le_right' (a b : Nat) : min a b ≤ b := Nat.min_le_right a b

theorem max_comm' (a b : Nat) : max a b = max b a := Nat.max_comm a b

theorem min_comm' (a b : Nat) : min a b = min b a := Nat.min_comm a b

theorem max_self' (a : Nat) : max a a = a := Nat.max_self a

theorem min_self' (a : Nat) : min a a = a := Nat.min_self a

end LeanFormal.IUT.XiFPaper.NatMaxMinActual
