/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips: gcd arithmetic for divisibility bookkeeping -/

namespace LeanFormal.IUT.XiFPaper.NatGcdActual

theorem gcd_dvd_left' (a b : Nat) : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b

theorem gcd_dvd_right' (a b : Nat) : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b

theorem dvd_gcd' {a b c : Nat} (h1 : c ∣ a) (h2 : c ∣ b) : c ∣ Nat.gcd a b :=
  Nat.dvd_gcd h1 h2

theorem gcd_comm' (a b : Nat) : Nat.gcd a b = Nat.gcd b a := Nat.gcd_comm a b

theorem gcd_pos_of_pos_left' {a b : Nat} (ha : 0 < a) : 0 < Nat.gcd a b :=
  Nat.gcd_pos_of_pos_left b ha

theorem gcd_pos_of_pos_right' {a b : Nat} (hb : 0 < b) : 0 < Nat.gcd a b := 
  Nat.gcd_pos_of_pos_right a hb

theorem gcd_self' (a : Nat) : Nat.gcd a a = a := Nat.gcd_self a

theorem gcd_one_left' (a : Nat) : Nat.gcd 1 a = 1 := Nat.gcd_one_left a

end LeanFormal.IUT.XiFPaper.NatGcdActual
