/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips: basic prime facts -/

namespace LeanFormal.IUT.XiFPaper.NatPrimeFactsActual

theorem prime_two' : Nat.Prime 2 := Nat.prime_two

theorem prime_three' : Nat.Prime 3 := Nat.prime_three

theorem not_prime_one' : ¬ Nat.Prime 1 := Nat.not_prime_one

theorem prime_pos' {p : Nat} (hp : Nat.Prime p) : 0 < p := hp.pos

theorem prime_two_le' {p : Nat} (hp : Nat.Prime p) : 2 ≤ p := hp.two_le

theorem prime_ne_zero' {p : Nat} (hp : Nat.Prime p) : p ≠ 0 := ne_of_gt hp.pos

theorem prime_ne_one' {p : Nat} (hp : Nat.Prime p) : p ≠ 1 := hp.ne_one

end LeanFormal.IUT.XiFPaper.NatPrimeFactsActual
