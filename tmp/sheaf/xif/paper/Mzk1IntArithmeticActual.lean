/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Cor 3.12: integer ring arithmetic wrappers -/

namespace LeanFormal.IUT.XiFPaper.IntArithmeticActual

variable {a b c : Int}

theorem int_add_assoc' : a + b + c = a + (b + c) := add_assoc a b c

theorem int_add_comm' : a + b = b + a := add_comm a b

theorem int_add_neg_cancel' : a + (-a) = 0 := add_neg_cancel a

theorem int_sub_eq_add_neg' : a - b = a + (-b) := sub_eq_add_neg a b

theorem int_neg_neg' : -(-a) = a := neg_neg a

theorem int_mul_comm' : a * b = b * a := mul_comm a b

theorem int_mul_add' : a * (b + c) = a * b + a * c := mul_add a b c

theorem int_add_mul' : (a + b) * c = a * c + b * c := add_mul a b c

theorem int_sub_self' : a - a = 0 := sub_self a

theorem int_add_sub_cancel' : a + b - b = a := add_sub_cancel_right a b

end LeanFormal.IUT.XiFPaper.IntArithmeticActual
