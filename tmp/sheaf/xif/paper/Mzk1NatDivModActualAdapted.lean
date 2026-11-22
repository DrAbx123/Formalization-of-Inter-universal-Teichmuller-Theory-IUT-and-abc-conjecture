/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Log-shell: natural division/modulo identities -/

namespace LeanFormal.IUT.XiFPaper.NatDivModActual

variable {a b : Nat}

theorem div_mul_le' : a / b * b ≤ a := Nat.div_mul_le_self a b

theorem mod_lt' (hb : 0 < b) : a % b < b := Nat.mod_lt a hb

theorem div_add_mod' : a / b * b + a % b = a := Nat.div_add_mod a b

theorem mod_add_div' : a % b + b * (a / b) = a := Nat.mod_add_div a b

theorem div_eq_of_lt' (h : a < b) : a / b = 0 := Nat.div_eq_of_lt h

theorem mod_eq_of_lt' (h : a < b) : a % b = a := Nat.mod_eq_of_lt h

theorem div_le_self' (hb : 0 < b) : a / b ≤ a := Nat.div_le_self a b

end LeanFormal.IUT.XiFPaper.NatDivModActual
