/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Section 0: strict natural-order facts -/

namespace LeanFormal.IUT.XiFPaper.NatOrderStrictActual

variable {a b : Nat}

theorem le_antisymm' (h1 : a ≤ b) (h2 : b ≤ a) : a = b := Nat.le_antisymm h1 h2

theorem lt_irrefl' : ¬ a < a := Nat.lt_irrefl a

theorem lt_asymm' (h : a < b) : ¬ b < a := Nat.lt_asymm h

theorem lt_of_le_of_ne' (h1 : a ≤ b) (h2 : a ≠ b) : a < b := Nat.lt_of_le_of_ne h1 h2

theorem le_of_not_lt' (h : ¬ b < a) : a ≤ b := Nat.le_of_not_lt h

theorem not_lt_of_le' (h : a ≤ b) : ¬ b < a := Nat.not_lt_of_le h

theorem not_le_of_lt' (h : a < b) : ¬ b ≤ a := Nat.not_le_of_lt h

end LeanFormal.IUT.XiFPaper.NatOrderStrictActual
