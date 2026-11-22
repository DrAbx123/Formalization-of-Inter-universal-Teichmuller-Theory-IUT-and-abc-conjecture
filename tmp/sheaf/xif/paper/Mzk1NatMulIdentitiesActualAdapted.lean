/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips: natural multiplication identities -/

namespace LeanFormal.IUT.XiFPaper.NatMulIdentitiesActual

variable {a b c : Nat}

theorem mul_one' : a * 1 = a := Nat.mul_one a

theorem one_mul' : 1 * a = a := Nat.one_mul a

theorem mul_zero' : a * 0 = 0 := Nat.mul_zero a

theorem zero_mul' : 0 * a = 0 := Nat.zero_mul a

theorem mul_comm' : a * b = b * a := Nat.mul_comm a b

theorem mul_assoc' : a * b * c = a * (b * c) := Nat.mul_assoc a b c

theorem mul_left_comm' : a * (b * c) = b * (a * c) := Nat.mul_left_comm a b c

theorem mul_right_comm' : a * b * c = a * c * b := Nat.mul_right_comm a b c

end LeanFormal.IUT.XiFPaper.NatMulIdentitiesActual
