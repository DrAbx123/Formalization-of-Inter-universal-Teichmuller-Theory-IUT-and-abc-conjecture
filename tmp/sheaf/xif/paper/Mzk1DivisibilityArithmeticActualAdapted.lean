/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips: divisibility arithmetic for exponent/degree bookkeeping -/

namespace LeanFormal.IUT.XiFPaper.DivisibilityArithmeticActual

variable {a b c : Nat}

theorem dvd_trans' (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := Nat.dvd_trans h1 h2

theorem dvd_antisymm' (h1 : a ∣ b) (h2 : b ∣ a) : a = b := Nat.dvd_antisymm h1 h2

theorem one_dvd' (a : Nat) : 1 ∣ a := one_dvd a

theorem dvd_zero' (a : Nat) : a ∣ 0 := dvd_zero a

theorem dvd_add' (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := dvd_add h1 h2

theorem dvd_sub' (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b - c := Nat.dvd_sub h1 h2

theorem dvd_mul_right' (a b : Nat) : a ∣ a * b := dvd_mul_right a b

theorem dvd_mul_left' (a b : Nat) : a ∣ b * a := dvd_mul_left a b

theorem dvd_mul_of_dvd_left' (h : a ∣ b) (c : Nat) : a ∣ b * c := dvd_mul_of_dvd_left h c

theorem dvd_mul_of_dvd_right' (h : a ∣ b) (c : Nat) : a ∣ c * b := dvd_mul_of_dvd_right h c

end LeanFormal.IUT.XiFPaper.DivisibilityArithmeticActual
